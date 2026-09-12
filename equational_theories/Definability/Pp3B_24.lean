import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq399 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq399 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq399
    | (have j0 := eq399 (σ X0) (σ X1)
       grind)
    | exact resolve eq399 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq404 X1 X0
       have i₂ := eq399 X1 X0
       grind)
    | exact superpose eq399 eq404
    | (have j0 := eq404 X1 X0
       have j1 := eq399 (σ X1) (σ X0)
       grind)
    | exact resolve eq404 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6872 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1016 x y
       grind)
    | exact superpose eq1016 eq16
    | (have j1 := eq1016 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1016 x y
       grind)
    | exact resolve eq16 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq6926 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6872
  have eq6949 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6926
       grind)
    | exact superpose eq6926 eq16
    | exact resolve eq16 eq6926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6958 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq6926
       grind)
    | exact superpose eq6926 eq12
    | exact resolve eq12 eq6926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6959 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq6926
       grind)
    | exact superpose eq6926 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6926
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6926
       grind)
    | exact resolve eq13 eq6926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6926
  have eq6980 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq6959
  have eq6989 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6980
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6980
    | exact resolve eq6980 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6980
  have eq6990 : (σ y) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6958
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6958
    | exact resolve eq6958 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6958
  have eq6992 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq399 eq6989
    | (have j1 := eq399 y x
       grind)
    | exact resolve eq6989 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989
  have eq6993 : (σ (M.op x y)) = (σ y) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq399 eq6990
    | (have j1 := eq399 y x
       grind)
    | exact resolve eq6990 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq6990
  have eq6995 : y = (M.op x y) := by grind
  clear eq6949 eq6992 eq6993
  have eq6997 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6995
       grind)
    | exact superpose eq6995 eq16
    | exact resolve eq16 eq6995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6999 : x ≠ y ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6995
       grind)
    | exact superpose eq6995 eq12
    | exact resolve eq12 eq6995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7000 : y ≠ y ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6995
       grind)
    | exact superpose eq6995 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6995
       grind)
    | exact resolve eq13 eq6995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6995
  have eq7021 : x = y ∨ y = (k y x) := by grind
  clear eq7000
  have eq7022 : y = (k y x) := by
    first
    | (have r₁ := eq6999
       have r₂ := eq7021
       grind)
    | exact resolve eq6999 eq7021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6999 eq7021
  have eq7028 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq404 y x
       have i₂ := eq7022
       grind)
    | exact superpose eq7022 eq404
    | (have j0 := eq404 y x
       grind)
    | exact resolve eq404 eq7022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq7022
  have eq7031 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7028
  have eq7037 : False := by grind
  exact eq7037

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq80 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq126 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq135 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq126
    | (have j0 := eq126 X0
       grind)
    | exact resolve eq126 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq126
  have eq137 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq135
    | (have j0 := eq135 X0
       grind)
    | exact resolve eq135 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq138 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq137 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq137 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq137 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq145 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq138 (σ X0)
       grind)
    | exact superpose eq138 eq15
    | exact resolve eq15 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq145 X0
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq145
    | exact resolve eq145 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq145
  have eq233 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq16
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq710 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq760 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq710
    | (have j0 := eq710 X0 X1
       grind)
    | exact resolve eq710 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq875 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq238 (τ X1) (τ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq238
    | (have j0 := eq238 (τ X0) (τ X1)
       grind)
    | exact resolve eq238 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq883 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq875 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq875
    | (have j0 := eq875 X0 X1
       grind)
    | exact resolve eq875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq886 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq883 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq883
    | (have j0 := eq883 X0 X1
       grind)
    | exact resolve eq883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq888 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq886 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq886
    | (have j0 := eq886 X0 X1
       grind)
    | exact resolve eq886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq889 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq890 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq889 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq889
    | (have j0 := eq889 X0 X1
       grind)
    | exact resolve eq889 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq891 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq890 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq890
    | (have j0 := eq890 X0 X1
       grind)
    | exact resolve eq890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq1030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq233
       have i₂ := eq760 y x
       grind)
    | exact superpose eq760 eq233
    | (have j1 := eq760 (σ x) (σ y)
       grind)
    | (have r₁ := eq233
       have r₂ := eq760 y x
       grind)
    | (have r₁ := eq233
       have r₂ := eq760 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq233
       have r₂ := eq760 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq233 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq760
  have eq1031 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1030
  have eq7805 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1031
       grind)
    | exact superpose eq1031 eq16
    | exact resolve eq16 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq7806 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7805
       have r₂ := eq152 x
       grind)
    | exact resolve eq7805 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7805
  have eq7906 : x ≠ x ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7806
       grind)
    | exact superpose eq7806 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq7806
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7806
       grind)
    | exact resolve eq12 eq7806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7806
  have eq7913 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7906
  have eq7918 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq238 x y
       have i₂ := eq7913
       grind)
    | exact superpose eq7913 eq238
    | (have j0 := eq238 x y
       grind)
    | exact resolve eq238 eq7913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq7913
  have eq7932 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7918
  have eq7933 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7932
  have eq8038 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7933
       grind)
    | exact superpose eq7933 eq16
    | exact resolve eq16 eq7933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8041 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq7933
       grind)
    | exact superpose eq7933 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7933
       grind)
    | exact resolve eq12 eq7933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7933
  have eq8048 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq8041
  have eq8055 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq8048
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8048
    | exact resolve eq8048 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8048
  have eq8161 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8055
       grind)
    | exact superpose eq8055 eq10
    | exact resolve eq10 eq8055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8055
  have eq8239 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq8161
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8161
    | exact resolve eq8161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8161
  have eq8255 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8239
       grind)
    | exact superpose eq8239 eq16
    | exact resolve eq16 eq8239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8239
  have eq8256 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq8255
       have r₂ := eq152 x
       grind)
    | exact resolve eq8255 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8255
  have eq8319 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq8256
       grind)
    | exact superpose eq8256 eq10
    | exact resolve eq10 eq8256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8256
  have eq8399 : x = (k y x) := by
    first
    | (have i₁ := eq8319
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8319
    | exact resolve eq8319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8319
  have eq8425 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq891 y x
       have i₂ := eq8399
       grind)
    | exact superpose eq8399 eq891
    | (have j0 := eq891 x y
       grind)
    | (have r₁ := eq891 y x
       have r₂ := eq8399
       grind)
    | exact resolve eq891 eq8399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq8399
  have eq8432 : x = y ∨ x = (M.op x y) := by grind
  clear eq8425
  have eq8584 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8432
       grind)
    | exact superpose eq8432 eq16
    | exact resolve eq16 eq8432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8432
  have eq8589 : x = (M.op x y) := by
    first
    | (have r₁ := eq8584
       have r₂ := eq152 x
       grind)
    | exact resolve eq8584 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8584
  have eq8593 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8038
       have i₂ := eq8589
       grind)
    | exact superpose eq8589 eq8038
    | exact resolve eq8038 eq8589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8038 eq8589
  have eq8603 : (σ x) = (σ y) := by grind
  clear eq8593
  have eq8749 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8603
       grind)
    | exact superpose eq8603 eq10
    | exact resolve eq10 eq8603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8603
  have eq8832 : x = y := by
    first
    | (have i₁ := eq8749
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8749
    | exact resolve eq8749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8749
  have eq8850 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8832
       grind)
    | exact superpose eq8832 eq16
    | exact resolve eq16 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8832
  have eq8856 : False := by grind
  exact eq8856

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq57
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq86
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq191 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq195 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq191 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq191 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq207 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       have j1 := eq80 X1 (σ X0)
       grind)
    | (have r₁ := eq195 X0 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq195 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq195
  have eq215 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq207
    | (have j0 := eq207 X0 X1
       grind)
    | exact resolve eq207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq216 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq215 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq222 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq216 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq216
    | exact resolve eq216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq216 x y
       grind)
    | exact superpose eq216 eq16
    | exact resolve eq16 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq292 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq222 X0 (τ X1)
       grind)
    | exact superpose eq222 eq18
    | exact resolve eq18 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq222
  have eq309 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq292
    | exact resolve eq292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq317 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq309
    | exact resolve eq309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq337 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq233
       have i₂ := eq317 x y
       grind)
    | exact superpose eq317 eq233
    | exact resolve eq233 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq317
  have eq338 : False := by grind
  exact eq338

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation2300 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X0) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq35 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq94 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq199 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq210 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq199
    | (have j0 := eq199 X0 X1 X2
       grind)
    | exact resolve eq199 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq199
  have eq1637 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0))))) X0) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (M.op X1 (M.op (τ X1) (M.op X1 (τ X1)))) X1
       have i₂ := eq9 (τ X1) X1
       grind)
    | exact superpose eq9 eq99
    | (have j0 := eq99 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1678 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op (τ X0) (M.op X1 (τ X0)))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1637 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1637
    | (have j0 := eq1637 X0 X1
       grind)
    | exact resolve eq1637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq4896 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k X3 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq210 X0 X1 X2
       grind)
    | exact superpose eq210 eq13
    | (have j0 := eq13 (M.op (σ X0) (k (σ X1) X2)) (k X3 (k (σ X1) X2))
       have j1 := eq210 X1 X2 X0
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq210 X0 X1 X2
       grind)
    | exact resolve eq13 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq65873 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq1678 X0 X1
       grind)
    | exact superpose eq1678 eq9
    | (have j1 := eq1678 X0 X1
       grind)
    | exact resolve eq9 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq65909 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65873 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq65873
    | (have j0 := eq65873 X0 X1
       grind)
    | exact resolve eq65873 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq65873
  have eq65910 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ (M.op X1 (M.op (τ X0) (M.op X1 (τ X0))))) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq65909 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65909
  have eq66014 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (k (σ (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0)))))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65910 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq65910
    | (have j0 := eq65910 (σ X0) X1
       grind)
    | exact resolve eq65910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65910
  have eq66298 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (k (σ (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0)))))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66014 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq66014
    | (have j0 := eq66014 X0 X1
       grind)
    | exact resolve eq66014 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66014
  have eq66310 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (k (σ (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0)))))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66298 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66298
    | (have j0 := eq66298 X0 X1
       grind)
    | exact resolve eq66298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66298
  have eq66318 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0))))) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66310 X0 X1
       have i₂ := eq15 (M.op X1 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0))))) X0
       grind)
    | exact superpose eq15 eq66310
    | (have j0 := eq66310 X0 X1
       grind)
    | exact resolve eq66310 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66310
  have eq66319 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (σ (k (M.op X1 (M.op X0 (M.op X1 X0))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66318 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66318
    | (have j0 := eq66318 X0 X1
       grind)
    | exact resolve eq66318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66318
  have eq214009 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4896 X0 X1 X2 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896
  have eq214010 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq214009 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214009
  have eq214019 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214010 X0 X1 X2
       have i₂ := eq35 X1 X2 X0
       grind)
    | exact superpose eq35 eq214010
    | (have j0 := eq214010 X0 X1 X2
       grind)
    | exact resolve eq214010 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq214010
  have eq214020 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq214019 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214019
  have eq214554 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq214020 (τ X0) X1 X2
       grind)
    | exact superpose eq214020 eq18
    | (have j1 := eq214020 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq214020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq214020
  have eq214882 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214554 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq214554
    | (have j0 := eq214554 X0 X1 X2
       grind)
    | exact resolve eq214554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214554
  have eq215046 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214882 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq214882
    | (have j0 := eq214882 X0 X1 X2
       grind)
    | exact resolve eq214882 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214882
  have eq215176 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq215046 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215046
    | (have j0 := eq215046 X0 X1 X2
       grind)
    | exact resolve eq215046 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215046
  have eq215413 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op X1 (k X0 X2)) ∨ (k X0 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq215176 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215176
    | exact resolve eq215176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215176
  have eq217354 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq217949 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k (M.op X2 (M.op X0 (M.op X2 X0))) X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217354 X0 X1
       have i₂ := eq66319 X0 X1
       grind)
    | exact superpose eq66319 eq217354
    | (have j1 := eq66319 X0 X2
       grind)
    | exact resolve eq217354 eq66319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66319 eq217354
  have eq434337 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op X1 (M.op X0 (M.op X1 X0))) X0) ∨ X0 = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (M.op X1 (M.op X0 (M.op X1 X0))) X0)
       have i₂ := eq217949 X0 X2 X1
       grind)
    | exact superpose eq217949 eq10
    | (have j1 := eq217949 X0 X2 X2
       grind)
    | exact resolve eq10 eq217949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217949
  have eq434819 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X0 (M.op X1 X0))) X0) = X0 ∨ X0 = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq434337 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq434337
    | (have j0 := eq434337 X0 X1 X2
       grind)
    | exact resolve eq434337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434337
  have eq437577 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ X0 = X3 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq215413 (M.op X1 (M.op X0 (M.op X1 X0))) X1 X0
       have i₂ := eq434819 X0 X1 x
       grind)
    | exact superpose eq434819 eq215413
    | (have j0 := eq215413 X1 (M.op X1 X0) X0
       have j1 := eq434819 X0 X1 X1
       grind)
    | exact resolve eq215413 eq434819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215413 eq434819
  have eq439296 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq437577 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437577
  have eq439297 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq439296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439296
  have eq439298 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq439297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439297
  have eq442005 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq439298 X0 (τ X1)
       grind)
    | exact superpose eq439298 eq19
    | (have j1 := eq439298 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq439298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq442379 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq439298 (σ X0) (σ X1)
       grind)
    | exact superpose eq439298 eq15
    | (have j1 := eq439298 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq439298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439298
  have eq446629 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq442005 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq442005
    | exact resolve eq442005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442005
  have eq447302 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq446629 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq446629
    | (have j0 := eq446629 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq446629 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446629
  have eq454278 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq442379 x y
       grind)
    | exact superpose eq442379 eq16
    | (have j1 := eq442379 x y
       grind)
    | exact resolve eq16 eq442379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442379
  have eq456491 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq454278
       have i₂ := eq447302 y x
       grind)
    | exact superpose eq447302 eq454278
    | (have j1 := eq447302 (σ x) (σ y)
       grind)
    | (have r₁ := eq454278
       have r₂ := eq447302 y x
       grind)
    | (have r₁ := eq454278
       have r₂ := eq447302 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq454278
       have r₂ := eq447302 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq454278 eq447302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447302 eq454278
  have eq456494 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq456491
  have eq456498 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq456494
       grind)
    | exact superpose eq456494 eq16
    | exact resolve eq16 eq456494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456494
  have eq456499 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq456498
       have r₂ := eq22 x
       grind)
    | exact resolve eq456498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456498
  have eq458581 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq456499
       grind)
    | exact superpose eq456499 eq16
    | exact resolve eq16 eq456499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458582 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq456499
       grind)
    | exact superpose eq456499 eq10
    | exact resolve eq10 eq456499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456499
  have eq459064 : x = y := by
    first
    | (have i₁ := eq458582
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq458582
    | exact resolve eq458582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458582
  have eq459065 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq458581
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq458581
    | exact resolve eq458581 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq458581
  have eq459068 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq459065
       have i₂ := eq459064
       grind)
    | exact superpose eq459064 eq459065
    | exact resolve eq459065 eq459064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459064 eq459065
  have eq459069 : False := by grind
  exact eq459069

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation2300 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq113 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq585 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq113 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq113 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq113 (M.op (τ X1) X1) X1
       grind)
    | exact resolve eq13 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq596 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq585 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq597 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq596 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq783 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2152 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq597
    | exact resolve eq597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq2203 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2152 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2152
    | (have j0 := eq2152 X0 X1
       grind)
    | exact resolve eq2152 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152
  have eq2245 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2203 X1 X0
       grind)
    | exact superpose eq2203 eq10
    | (have j1 := eq2203 X1 X0
       grind)
    | exact resolve eq10 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2287 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2245 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2245
    | (have j0 := eq2245 X0 X1
       grind)
    | exact resolve eq2245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq2302 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq2287 X0 (σ X1)
       grind)
    | exact superpose eq2287 eq28
    | (have j1 := eq2287 X0 (σ X1)
       grind)
    | exact resolve eq28 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2287
  have eq4065 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2302 (σ X0) X1
       grind)
    | exact superpose eq2302 eq37
    | (have j1 := eq2302 (σ X0) X1
       grind)
    | exact resolve eq37 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2302
  have eq4130 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4065 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4065
    | (have j0 := eq4065 X0 X1
       grind)
    | exact resolve eq4065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065
  have eq4162 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4130 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4130
    | (have j0 := eq4130 X0 X1
       grind)
    | exact resolve eq4130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130
  have eq4172 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4162 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4162
    | (have j0 := eq4162 X0 X1
       grind)
    | exact resolve eq4162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4162
  have eq4373 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4172 X0 X1
       grind)
    | exact superpose eq4172 eq11
    | (have j1 := eq4172 X0 X1
       grind)
    | exact resolve eq11 eq4172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172
  have eq5234 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4373 x y
       grind)
    | exact superpose eq4373 eq16
    | (have j1 := eq4373 x y
       grind)
    | exact resolve eq16 eq4373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4373
  have eq5263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5234
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5234
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5234
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5234
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5234 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5234
       have i₂ := eq2203 y x
       grind)
    | exact superpose eq2203 eq5234
    | (have j1 := eq2203 y x
       grind)
    | (have r₁ := eq5234
       have r₂ := eq2203 y x
       grind)
    | (have r₁ := eq5234
       have r₂ := eq2203 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5234
       have r₂ := eq2203 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5234 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203 eq5234
  have eq5267 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5264
  have eq5268 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq5267
  have eq5269 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5263
  have eq5270 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5269
  have eq5274 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5268
       grind)
    | exact superpose eq5268 eq16
    | exact resolve eq16 eq5268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5268
  have eq5275 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5274
       have r₂ := eq22 x
       grind)
    | exact resolve eq5274 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5274
  have eq5281 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq783 x y
       have i₂ := eq5275
       grind)
    | exact superpose eq5275 eq783
    | (have j0 := eq783 x y
       grind)
    | exact resolve eq783 eq5275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq5275
  have eq5286 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5281
  have eq5287 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5286
  have eq5291 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5270
       grind)
    | exact superpose eq5270 eq16
    | exact resolve eq16 eq5270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5270
  have eq5292 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5291
       have r₂ := eq22 x
       grind)
    | exact resolve eq5291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291
  have eq5302 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5287
       grind)
    | exact superpose eq5287 eq16
    | exact resolve eq16 eq5287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5287
  have eq5324 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5302
       have i₂ := eq5292
       grind)
    | exact superpose eq5292 eq5302
    | exact resolve eq5302 eq5292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5292 eq5302
  have eq5325 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5324
  have eq5326 : (σ x) = (σ y) := by grind
  clear eq5325
  have eq5327 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5326
       grind)
    | exact superpose eq5326 eq16
    | exact resolve eq16 eq5326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5328 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5326
       grind)
    | exact superpose eq5326 eq10
    | exact resolve eq10 eq5326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5326
  have eq5380 : x = y := by
    first
    | (have i₁ := eq5328
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5328
    | exact resolve eq5328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5328
  have eq5381 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5327
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5327
    | exact resolve eq5327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5327
  have eq5382 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5381
       have i₂ := eq5380
       grind)
    | exact superpose eq5380 eq5381
    | exact resolve eq5381 eq5380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5380 eq5381
  have eq5383 : False := by grind
  exact eq5383

/-- `Equation2340`: `x = (y ◇ (y ◇ (y ◇ y))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxy_pyx_Equation2340 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2340 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2340.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq41 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) ≠ (M.op X0 (M.op X0 (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X0 (M.op X0 X0)))
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X0 X0))) X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X1 (M.op X1 X1)))
       have r₂ := eq9 (M.op X1 (M.op X1 (M.op X1 X1))) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq95 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op X1 (M.op X1 (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X1 (M.op X1 X1)))
       have i₂ := eq42 X1 (τ X0)
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq105 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq156 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq64 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq64 X0
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq159 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq156 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq156 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq225 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105 x y
       grind)
    | exact superpose eq105 eq16
    | (have j1 := eq105 x y
       grind)
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq230 : ∀ X0 : G, (σ (M.op X0 (M.op X0 (M.op X0 X0)))) ≠ (σ (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0))))) ∨ (σ (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq158 (M.op X0 (M.op X0 (M.op X0 X0)))
       have i₂ := eq42 X0 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq42 eq158
    | (have j0 := eq158 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact resolve eq158 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq238 : ∀ X0 : G, (σ (M.op X0 (M.op X0 (M.op X0 X0)))) ≠ (σ (M.op X0 (M.op X0 (M.op X0 X0)))) ∨ (σ (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq230 X0
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X0 X0))) X0
       grind)
    | exact superpose eq9 eq230
    | (have j0 := eq230 X0
       grind)
    | exact resolve eq230 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq239 : ∀ X0 : G, (σ (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0
    first
    | (have j0 := eq238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq250 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 (M.op X0 X0)))) ≠ (σ (M.op (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 (M.op X0 X0))))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq159 (M.op X0 (M.op X0 (M.op X0 X0))) X1
       have i₂ := eq42 X0 (M.op X0 (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq42 eq159
    | (have j0 := eq159 (M.op X0 (M.op X0 (M.op X0 X0))) X1
       grind)
    | exact resolve eq159 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq159
  have eq258 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 (M.op X0 X0)))) ≠ (σ (M.op X0 (M.op X0 (M.op X0 X0)))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X0 X0))) X0
       grind)
    | exact superpose eq9 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq259 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq258 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq500 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq259 x X0
       have i₂ := eq95 X0 x
       grind)
    | exact superpose eq95 eq259
    | exact resolve eq259 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq259
  have eq559 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq500 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq500
    | exact resolve eq500 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq601 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq559 X0
       grind)
    | exact superpose eq559 eq9
    | exact resolve eq9 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 (M.op X0 X0)))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq601 (M.op X0 (M.op X0 (M.op X0 X0))) X1
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X0 X0))) X0
       grind)
    | exact superpose eq9 eq601
    | exact resolve eq601 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq914 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 (M.op X0 X0))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq849 X0 X1
       have i₂ := eq239 X0
       grind)
    | exact superpose eq239 eq849
    | exact resolve eq849 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq945 : ∀ X0 X1 : G, (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq914 X0 X1
       have i₂ := eq239 X0
       grind)
    | exact superpose eq239 eq914
    | exact resolve eq914 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq914
  have eq3789 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq225
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq225
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq225
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq225
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq225 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq3790 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq3789
  have eq3791 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3790
       have i₂ := eq559 x
       grind)
    | exact superpose eq559 eq3790
    | exact resolve eq3790 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq58820 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3791
       grind)
    | exact superpose eq3791 eq16
    | exact resolve eq16 eq3791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq58821 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq58820
       have r₂ := eq559 x
       grind)
    | exact resolve eq58820 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58820
  have eq58823 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq58821
       grind)
    | exact superpose eq58821 eq10
    | exact resolve eq10 eq58821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58821
  have eq58898 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq58823
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq58823
    | exact resolve eq58823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58823
  have eq58920 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58898
       grind)
    | exact superpose eq58898 eq16
    | exact resolve eq16 eq58898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58898
  have eq58921 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq58920
       have r₂ := eq559 x
       grind)
    | exact resolve eq58920 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq58920
  have eq59122 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq58921
       grind)
    | exact superpose eq58921 eq10
    | exact resolve eq10 eq58921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58921
  have eq59202 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq59122
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq59122
    | exact resolve eq59122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59122
  have eq59203 : x = (M.op x x) := by grind
  clear eq59202
  have eq59222 : ∀ X0 : G, (M.op (M.op x (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x
       have i₂ := eq59203
       grind)
    | exact superpose eq59203 eq9
    | exact resolve eq9 eq59203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59255 : ∀ X0 : G, (M.op (σ (M.op x (M.op x x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq945 x X0
       have i₂ := eq59203
       grind)
    | exact superpose eq59203 eq945
    | exact resolve eq945 eq59203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq59362 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59255 X0
       have i₂ := eq59203
       grind)
    | exact superpose eq59203 eq59255
    | exact resolve eq59255 eq59203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59255
  have eq59392 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59222 X0
       have i₂ := eq59203
       grind)
    | exact superpose eq59203 eq59222
    | exact resolve eq59222 eq59203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59222
  have eq59444 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59362 X0
       have i₂ := eq59203
       grind)
    | exact superpose eq59203 eq59362
    | exact resolve eq59362 eq59203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59362
  have eq59474 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59392 X0
       have i₂ := eq59203
       grind)
    | exact superpose eq59203 eq59392
    | exact resolve eq59392 eq59203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59203 eq59392
  have eq64489 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59444 (σ y)
       grind)
    | exact superpose eq59444 eq16
    | exact resolve eq16 eq59444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59444
  have eq64945 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq64489
       have i₂ := eq59474 y
       grind)
    | exact superpose eq59474 eq64489
    | exact resolve eq64489 eq59474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59474 eq64489
  have eq64946 : False := by grind
  exact eq64946

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq105 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq105 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq106 (σ X0)
       grind)
    | exact superpose eq106 eq10
    | exact resolve eq10 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq49
    | exact resolve eq49 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq112 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq111
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq111
    | exact resolve eq111 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq108
    | exact resolve eq108 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq108
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq247 : x = (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq441 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X1 X3))) = (M.op (M.op X4 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 X4 (M.op X1 (M.op X2 (M.op X0 X2))) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op X3 X4))) = (M.op (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1)))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X3 X5 (M.op X3 (M.op X0 X2)) X4
       have i₂ := eq52 X2 X3 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op y X0))) = (M.op (M.op X1 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y X1 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y X1 x X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X1 X2)
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X3 X2)) X1)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op X2 (M.op X3 X2)) X0 X2
       have i₂ := eq52 (M.op X2 (M.op X3 X2)) (M.op X2 (M.op X3 X2)) X0 X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X3 (M.op X4 X3)) X4 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq53 X4 X1 X0 X3
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1055 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq452
    | exact resolve eq452 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1077 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq1055 eq452
    | exact resolve eq452 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq1077 eq14
    | exact resolve eq14 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1125 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op X1 X0) X1) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1055 eq457
    | exact resolve eq457 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1130 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq457 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq457
    | (have j0 := eq457 X0 x y
       grind)
    | exact resolve eq457 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1141 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X1)) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq457 (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X1) X2 X3
       have i₂ := eq457 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq457 eq457
    | exact resolve eq457 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : (M.op y (M.op x y)) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq247 eq457
    | exact resolve eq457 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq457
  have eq1238 : ∀ X0 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq452 X0 y X0
       have i₂ := eq1108 X0
       grind)
    | (have i₁ := eq452 x y x
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq452
    | exact resolve eq452 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq8411 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X2 (M.op X0 (M.op X1 (M.op X2 X1)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq515 X3 X2 X2 X0
       have i₂ := eq52 X2 X2 X0 X1
       grind)
    | exact superpose eq52 eq515
    | exact resolve eq515 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq515
  have eq9637 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq433 (M.op X1 (M.op x X1)) sF4 sF3
       have i₂ := eq53 sF3 X1 x sF4
       grind)
    | exact superpose eq53 eq433
    | exact resolve eq433 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq25031 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X6 (M.op X4 (M.op X1 X4))) X6) = (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq441 (M.op X4 (M.op X1 X4)) (M.op X2 (M.op X0 X2)) x X5 X6
       have i₂ := eq520 X0 X2 x X4 X1
       grind)
    | exact superpose eq520 eq441
    | exact resolve eq441 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq520
  have eq25180 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) = X1 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq25031 X0 X1 X2 x X5 x
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq25031
    | exact resolve eq25031 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25031
  have eq32119 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op X2 y) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq442 (M.op X2 y) y X2 X1 X3 x
       have i₂ := eq445 (M.op X2 y) X0
       grind)
    | exact superpose eq445 eq442
    | exact resolve eq442 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq445
  have eq32607 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq32119 X0 X1 x X3
       have i₂ := eq1108 x
       grind)
    | (have i₁ := eq32119 X0 X1 x X3
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq32119
    | (have j0 := eq32119 X0 X1 x X3
       grind)
    | exact resolve eq32119 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq32119
  have eq32934 : ∀ X1 X3 : G, y = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq1130 eq32607
    | exact resolve eq32607 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq32607
  have eq85075 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X1 X0) X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9637 (M.op (M.op sF4 sF2) (M.op (M.op X1 x) X1)) (M.op sF4 sF2)
       have i₂ := eq458 (M.op sF4 sF2) X1 x (M.op sF4 sF2)
       grind)
    | exact superpose eq458 eq9637
    | exact resolve eq9637 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq107983 : ∀ X0 X2 : G, (M.op (M.op x y) x) = (M.op X0 (M.op y (M.op X2 (M.op X0 X2)))) := by
    intro X0 X2
    first
    | exact superpose eq32934 eq53
    | exact resolve eq53 eq32934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq32934
  have eq152520 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X0 X1) (σ y))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq9637 eq1141
    | exact resolve eq1141 eq9637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq9637
  have eq419377 : ∀ X0 X1 : G, y = (M.op (M.op y x) (M.op X0 (M.op (M.op X1 (M.op y X1)) X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq25180 y y X1 X0
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq25180
    | exact resolve eq25180 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq419433 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq419377 x x
       have i₂ := eq25180 y x x x
       grind)
    | exact superpose eq25180 eq419377
    | exact resolve eq419377 eq25180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25180 eq419377
  have eq448713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq419433 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq419433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419433
  have eq448720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq448713
    | exact resolve eq448713 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448713
  have eq448731 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq448720
       have r₂ := eq27
       grind)
    | exact resolve eq448720 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448720
  have eq448990 : (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (σ x)) (σ y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq448731 eq152520
    | exact resolve eq152520 eq448731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152520 eq448731
  have eq448995 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq85075 eq448990
    | exact resolve eq448990 eq85075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85075 eq448990
  have eq451649 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq448995 eq112
    | exact resolve eq112 eq448995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448995
  have eq452069 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq451649
    | exact resolve eq451649 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451649
  have eq452070 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq452069
  have eq452205 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq452070
       grind)
    | exact superpose eq452070 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq452070
       grind)
    | exact resolve eq13 eq452070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452208 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq602 x X0
       have i₂ := eq452070
       grind)
    | exact superpose eq452070 eq602
    | (have j0 := eq602 x X0
       grind)
    | exact resolve eq602 eq452070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq452306 : x = (M.op (M.op x x) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1125 x x
       have i₂ := eq452070
       grind)
    | exact superpose eq452070 eq1125
    | exact resolve eq1125 eq452070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq452070
  have eq452430 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq452208 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452208
  have eq452431 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq452205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452205
  have eq452477 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1148 eq452306
    | exact resolve eq452306 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq452306
  have eq452543 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq452430 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq452430
    | (have j0 := eq452430 X0
       grind)
    | exact resolve eq452430 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452430
  have eq452932 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op y (M.op X0 (M.op (M.op x y) x))))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq452477 eq8411
    | exact resolve eq8411 eq452477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8411
  have eq453002 : (M.op (M.op x y) x) = (M.op y (M.op y (M.op (M.op x y) x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq452477 eq107983
    | exact resolve eq107983 eq452477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107983 eq452477
  have eq453020 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1238 eq453002
    | exact resolve eq453002 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453002
  have eq453075 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1238 eq452932
    | exact resolve eq452932 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq452932
  have eq472464 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq452431 sF0
       grind)
    | exact superpose eq452431 eq129
    | exact resolve eq129 eq452431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq452431
  have eq821919 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq453020 eq472464
    | exact resolve eq472464 eq453020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453020 eq472464
  have eq821997 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq821919
  have eq822004 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq821997
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq821997
    | exact resolve eq821997 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821997
  have eq822016 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq822004 eq452543
    | exact resolve eq452543 eq822004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452543 eq822004
  have eq822024 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq822016
  have eq825266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq822024 eq453075
    | exact resolve eq453075 eq822024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453075 eq822024
  have eq825269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq825266
  have eq825273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq825269
    | exact resolve eq825269 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825269
  have eq825517 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq825273
       have r₂ := eq27
       grind)
    | exact resolve eq825273 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825273
  have eq825597 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq825517 eq29
    | exact resolve eq29 eq825517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq825517
  have eq825984 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq825597
    | exact resolve eq825597 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq825597
  have eq825985 : x = y := by grind
  clear eq825984
  have eq826016 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq825985
       grind)
    | exact superpose eq825985 eq18
    | exact resolve eq18 eq825985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq826017 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq825985
       grind)
    | exact superpose eq825985 eq24
    | exact resolve eq24 eq825985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq825985
  have eq826417 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq826017
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq826017
    | exact resolve eq826017 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq826017
  have eq830174 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq826417 eq26
    | exact resolve eq26 eq826417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq826417
  have eq831606 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq830174 eq112
    | exact resolve eq112 eq830174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq830174
  have eq832300 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq831606
       have i₂ := eq826016
       grind)
    | exact superpose eq826016 eq831606
    | exact resolve eq831606 eq826016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826016 eq831606
  have eq832549 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq832300 eq15
    | exact resolve eq15 eq832300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832300
  have eq832635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq832549
    | exact resolve eq832549 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq832549
  have eq832656 : False := by grind
  exact eq832656

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pxx_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X1 X3))) = (M.op (M.op X4 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 X1 X4 (M.op X1 (M.op X2 (M.op X0 X2))) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq51 X2 X0 X1 x
       grind)
    | exact superpose eq51 eq9
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq124 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq124 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq124 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq125 (σ X0)
       grind)
    | exact superpose eq125 eq15
    | exact resolve eq15 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq128 X0
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq128
    | exact resolve eq128 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq128
  have eq150 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 (σ X0) (σ X0)
       have i₂ := eq139 X0
       grind)
    | exact superpose eq139 eq79
    | exact resolve eq79 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq169 (σ X1) (σ X0)
       grind)
    | exact superpose eq169 eq15
    | (have j1 := eq169 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq139 X1
       grind)
    | exact superpose eq139 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq435 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X3 (M.op X4 X3)) X4 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq52 X4 X1 X0 X3
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq52
  have eq694 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq197 x y
       grind)
    | exact superpose eq197 eq16
    | (have j1 := eq197 x y
       grind)
    | exact resolve eq16 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq26241 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X6 (M.op X4 (M.op X1 X4))) X6) = (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq70 (M.op X4 (M.op X1 X4)) (M.op X2 (M.op X0 X2)) x X5 X6
       have i₂ := eq435 X0 X2 x X4 X1
       grind)
    | exact superpose eq435 eq70
    | exact resolve eq70 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq435
  have eq26507 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) = X1 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq26241 X0 X1 X2 x X5 x
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq26241
    | exact resolve eq26241 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26241
  have eq26605 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq694
       have i₂ := eq169 y x
       grind)
    | exact superpose eq169 eq694
    | (have j1 := eq169 y x
       grind)
    | exact resolve eq694 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq694
  have eq26606 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq26605
  have eq66737 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ (M.op y y))) X0) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq79 X0 (σ y) (σ x)
       have i₂ := eq26606
       grind)
    | exact superpose eq26606 eq79
    | exact resolve eq79 eq26606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq26606
  have eq66863 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66737 x
       have i₂ := eq150 y x
       grind)
    | exact superpose eq150 eq66737
    | exact resolve eq66737 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq66737
  have eq67032 : ∀ X0 X1 : G, y = (M.op (M.op y x) (M.op X0 (M.op (M.op X1 (M.op y X1)) X0))) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq26507 y y X1 X0
       have i₂ := eq66863
       grind)
    | exact superpose eq66863 eq26507
    | exact resolve eq26507 eq66863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66863
  have eq67035 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67032 x x
       have i₂ := eq26507 y x x x
       grind)
    | exact superpose eq26507 eq67032
    | exact resolve eq67032 eq26507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26507 eq67032
  have eq67062 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq67035
       grind)
    | exact superpose eq67035 eq10
    | exact resolve eq10 eq67035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67035
  have eq67106 : x = y ∨ x = y := by
    first
    | (have i₁ := eq67062
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq67062
    | exact resolve eq67062 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67062
  have eq67107 : x = y := by grind
  clear eq67106
  have eq67111 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67107
       grind)
    | exact superpose eq67107 eq16
    | exact resolve eq16 eq67107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67107
  have eq67112 : False := by grind
  exact eq67112
