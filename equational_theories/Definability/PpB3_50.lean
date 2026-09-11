import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyy_pxy_Equation335 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law335 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq47 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq345 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq352 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq345
    | (have j0 := eq345 X0 X1
       grind)
    | exact resolve eq345 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq2360 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq344
    | exact resolve eq344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq2413 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2360 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2360
    | (have j0 := eq2360 X0 X1
       grind)
    | exact resolve eq2360 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2736 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq352 x y
       grind)
    | exact superpose eq352 eq16
    | (have j1 := eq352 x y
       grind)
    | exact resolve eq16 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq7094 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2736
       have i₂ := eq2413 y x
       grind)
    | exact superpose eq2413 eq2736
    | (have j1 := eq2413 y x
       grind)
    | (have r₁ := eq2736
       have r₂ := eq2413 y x
       grind)
    | (have r₁ := eq2736
       have r₂ := eq2413 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2736
       have r₂ := eq2413 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2736 eq2413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413 eq2736
  have eq7095 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq7094
  have eq9856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7095
       grind)
    | exact superpose eq7095 eq16
    | exact resolve eq16 eq7095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7095
  have eq9857 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq9856
       have r₂ := eq24 x
       grind)
    | exact resolve eq9856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9856
  have eq9859 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9857
       grind)
    | exact superpose eq9857 eq10
    | exact resolve eq10 eq9857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9857
  have eq9911 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9859
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9859
    | exact resolve eq9859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9859
  have eq9913 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9911
       grind)
    | exact superpose eq9911 eq16
    | exact resolve eq16 eq9911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9911
  have eq9914 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9913
       have r₂ := eq24 x
       grind)
    | exact resolve eq9913 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9913
  have eq9923 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq9914
       grind)
    | exact superpose eq9914 eq10
    | exact resolve eq10 eq9914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9914
  have eq9984 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9923
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq9923
    | exact resolve eq9923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9923
  have eq9985 : y = (M.op x x) := by grind
  clear eq9984
  have eq9989 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq9985
       grind)
    | exact superpose eq9985 eq47
    | exact resolve eq47 eq9985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq10041 : y = (M.op x y) := by
    first
    | (have i₁ := eq9 x x
       have i₂ := eq9985
       grind)
    | exact superpose eq9985 eq9
    | exact resolve eq9 eq9985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9985
  have eq10214 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9989
       grind)
    | exact superpose eq9989 eq16
    | exact resolve eq16 eq9989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9989
  have eq10236 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq10214
       have i₂ := eq10041
       grind)
    | exact superpose eq10041 eq10214
    | exact resolve eq10214 eq10041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10041 eq10214
  have eq10237 : False := by grind
  exact eq10237

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyx_pxy_Equation335 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law335 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X0 X1)
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1)
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq113
    | exact resolve eq113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq110
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq208 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X1 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq114
    | exact resolve eq114 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X1 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq208
    | exact resolve eq208 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq359 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq360 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq361 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq38
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq38 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq2332 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq359
    | exact resolve eq359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq2383 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2332 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2332
    | (have j0 := eq2332 X0 X1
       grind)
    | exact resolve eq2332 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2332
  have eq2826 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq360 x y
       grind)
    | exact superpose eq360 eq16
    | (have j1 := eq360 x y
       grind)
    | exact resolve eq16 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2837 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq360 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq12146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2826
       have i₂ := eq2383 y x
       grind)
    | exact superpose eq2383 eq2826
    | (have j1 := eq2383 (σ y) (σ x)
       grind)
    | (have r₁ := eq2826
       have r₂ := eq2383 y x
       grind)
    | (have r₁ := eq2826
       have r₂ := eq2383 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2826
       have r₂ := eq2383 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2826 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383 eq2826
  have eq12147 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12146
  have eq18669 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12147
       grind)
    | exact superpose eq12147 eq16
    | exact resolve eq16 eq12147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12147
  have eq18670 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18669
       have r₂ := eq23 x
       grind)
    | exact resolve eq18669 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18669
  have eq18671 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq18670
       grind)
    | exact superpose eq18670 eq9
    | exact resolve eq9 eq18670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18673 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq18 y x
       have i₂ := eq18670
       grind)
    | exact superpose eq18670 eq18
    | exact resolve eq18 eq18670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18680 : x = (M.op (M.op y x) (M.op (M.op y x) x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq231 x y
       have i₂ := eq18670
       grind)
    | exact superpose eq18670 eq231
    | exact resolve eq231 eq18670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18670
  have eq18684 : x = (M.op x (M.op y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18680
       have i₂ := eq9 x (M.op y x)
       grind)
    | exact superpose eq9 eq18680
    | exact resolve eq18680 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18680
  have eq18688 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq18671
       grind)
    | exact superpose eq18671 eq9
    | exact resolve eq9 eq18671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18705 : x = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18684
       have i₂ := eq18671
       grind)
    | exact superpose eq18671 eq18684
    | exact resolve eq18684 eq18671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18671 eq18684
  have eq18723 : x = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18705
  have eq18731 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18723
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq18723
    | exact resolve eq18723 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18723
  have eq18734 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq18731
       grind)
    | exact superpose eq18731 eq9
    | exact resolve eq9 eq18731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18743 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ y) (σ x)) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq231 (σ x) (σ y)
       have i₂ := eq18731
       grind)
    | exact superpose eq18731 eq231
    | exact resolve eq231 eq18731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq18731
  have eq18749 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18743
       have i₂ := eq9 (σ x) (M.op (σ y) (σ x))
       grind)
    | exact superpose eq9 eq18743
    | exact resolve eq18743 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18743
  have eq18755 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18734
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq18734
    | exact resolve eq18734 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18734
  have eq29790 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18749
       have i₂ := eq18755
       grind)
    | exact superpose eq18755 eq18749
    | exact resolve eq18749 eq18755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18749 eq18755
  have eq29815 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq29790
  have eq29825 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29815
       have i₂ := eq46 x
       grind)
    | exact superpose eq46 eq29815
    | exact resolve eq29815 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq29815
  have eq29827 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29825
       grind)
    | exact superpose eq29825 eq10
    | exact resolve eq10 eq29825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29825
  have eq29890 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29827
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29827
    | exact resolve eq29827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29827
  have eq29892 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29890
       grind)
    | exact superpose eq29890 eq16
    | exact resolve eq16 eq29890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29890
  have eq29945 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29892
       have r₂ := eq23 x
       grind)
    | exact resolve eq29892 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29892
  have eq29961 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq29945
       grind)
    | exact superpose eq29945 eq10
    | exact resolve eq10 eq29945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29945
  have eq30038 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29961
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29961
    | exact resolve eq29961 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29961
  have eq30039 : x = (M.op x x) := by grind
  clear eq30038
  have eq38240 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq18673
       grind)
    | exact superpose eq18673 eq9
    | exact resolve eq9 eq18673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18673
  have eq38269 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq38240
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq38240
    | exact resolve eq38240 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38240
  have eq38279 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq38269
       have i₂ := eq30039
       grind)
    | exact superpose eq30039 eq38269
    | exact resolve eq38269 eq30039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38269
  have eq38281 : x = (M.op x (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38279
       have i₂ := eq30039
       grind)
    | exact superpose eq30039 eq38279
    | exact resolve eq38279 eq30039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38279
  have eq38296 : (M.op y x) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq114 x y
       have i₂ := eq38281
       grind)
    | exact superpose eq38281 eq114
    | exact resolve eq114 eq38281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38320 : (M.op y x) = (M.op x (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38296
       have i₂ := eq18 y x
       grind)
    | exact superpose eq18 eq38296
    | exact resolve eq38296 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38296
  have eq44552 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18688
       grind)
    | exact superpose eq18688 eq16
    | exact resolve eq16 eq18688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18688
  have eq44589 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44552
       have i₂ := eq30039
       grind)
    | exact superpose eq30039 eq44552
    | exact resolve eq44552 eq30039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30039 eq44552
  have eq57801 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38281
       have i₂ := eq38320
       grind)
    | exact superpose eq38320 eq38281
    | exact resolve eq38281 eq38320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38281 eq38320
  have eq57826 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq57801
  have eq57861 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq361 y (σ x)
       have i₂ := eq57826
       grind)
    | exact superpose eq57826 eq361
    | (have j0 := eq361 x (σ y)
       grind)
    | exact resolve eq361 eq57826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq57826
  have eq57883 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq57861
  have eq57905 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq57883
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq57883
    | exact resolve eq57883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57883
  have eq57930 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq57905
       grind)
    | exact superpose eq57905 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq57905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57963 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq57930
  have eq58598 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq57963
       grind)
    | exact superpose eq57963 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq57963
       grind)
    | exact resolve eq13 eq57963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57963
  have eq58614 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq58598
  have eq58615 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq58614
  have eq58876 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57905
       have i₂ := eq58615
       grind)
    | exact superpose eq58615 eq57905
    | exact resolve eq57905 eq58615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57905 eq58615
  have eq58936 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq58876
  have eq58949 : (σ x) ≠ (σ x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq44589
       have i₂ := eq58936
       grind)
    | exact superpose eq58936 eq44589
    | exact resolve eq44589 eq58936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44589 eq58936
  have eq58980 : (σ x) ≠ (σ x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58949
  have eq58981 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58980
  have eq59023 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq58981
       grind)
    | exact superpose eq58981 eq9
    | exact resolve eq9 eq58981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59125 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq58981
       have i₂ := eq59023
       grind)
    | exact superpose eq59023 eq58981
    | exact resolve eq58981 eq59023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58981 eq59023
  have eq59142 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59125
  have eq59212 : (σ x) = (σ y) ∨ x = (M.op (M.op y x) (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq114 y x
       have i₂ := eq59142
       grind)
    | exact superpose eq59142 eq114
    | exact resolve eq114 eq59142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59142
  have eq59782 : y = (τ (σ x)) ∨ x = (M.op (M.op y x) (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq59212
       grind)
    | exact superpose eq59212 eq10
    | exact resolve eq10 eq59212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59212
  have eq59860 : x = y ∨ x = (M.op (M.op y x) (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq59782
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq59782
    | exact resolve eq59782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59782
  have eq59861 : x = y ∨ x = (M.op (M.op y x) (M.op y x)) := by grind
  clear eq59860
  have eq59864 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59861
       grind)
    | exact superpose eq59861 eq16
    | exact resolve eq16 eq59861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59861
  have eq59892 : x = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have r₁ := eq59864
       have r₂ := eq23 x
       grind)
    | exact resolve eq59864 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59864
  have eq60150 : x = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq9 (M.op y x) (M.op y x)
       have i₂ := eq59892
       grind)
    | exact superpose eq59892 eq9
    | exact resolve eq9 eq59892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60151 : (M.op x (M.op y x)) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq18 (M.op y x) (M.op y x)
       have i₂ := eq59892
       grind)
    | exact superpose eq59892 eq18
    | exact resolve eq18 eq59892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60153 : x = (M.op x (M.op (M.op y x) x)) := by
    first
    | (have i₁ := eq114 (M.op y x) (M.op y x)
       have i₂ := eq59892
       grind)
    | exact superpose eq59892 eq114
    | exact resolve eq114 eq59892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59892
  have eq60420 : (M.op x (M.op y x)) = (M.op (M.op y x) (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq18 x (M.op y x)
       have i₂ := eq60150
       grind)
    | exact superpose eq60150 eq18
    | exact resolve eq18 eq60150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60423 : (M.op x (M.op x (M.op y x))) = (M.op (M.op (M.op y x) (M.op x (M.op y x))) x) := by
    first
    | (have i₁ := eq117 (M.op y x) x
       have i₂ := eq60150
       grind)
    | exact superpose eq60150 eq117
    | exact resolve eq117 eq60150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq60150
  have eq60444 : (M.op (M.op y x) x) = (M.op (M.op (M.op y x) (M.op x (M.op y x))) x) := by
    first
    | (have i₁ := eq60423
       have i₂ := eq9 (M.op y x) x
       grind)
    | exact superpose eq9 eq60423
    | exact resolve eq60423 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60423
  have eq60457 : (M.op (M.op x (M.op y x)) x) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq60444
       have i₂ := eq60420
       grind)
    | exact superpose eq60420 eq60444
    | exact resolve eq60444 eq60420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60420 eq60444
  have eq60466 : (M.op x (M.op y x)) = (M.op (M.op x (M.op y x)) x) := by
    first
    | (have i₁ := eq60457
       have i₂ := eq60151
       grind)
    | exact superpose eq60151 eq60457
    | exact resolve eq60457 eq60151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60151 eq60457
  have eq60472 : (M.op x (M.op y x)) = (M.op x (M.op (M.op y x) x)) := by
    first
    | (have i₁ := eq60466
       have i₂ := eq18 (M.op y x) x
       grind)
    | exact superpose eq18 eq60466
    | exact resolve eq60466 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60466
  have eq60475 : x = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq60472
       have i₂ := eq60153
       grind)
    | exact superpose eq60153 eq60472
    | exact resolve eq60472 eq60153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60153 eq60472
  have eq60512 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq114 x y
       have i₂ := eq60475
       grind)
    | exact superpose eq60475 eq114
    | exact resolve eq114 eq60475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq60545 : (M.op y x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq60512
       have i₂ := eq18 y x
       grind)
    | exact superpose eq18 eq60512
    | exact resolve eq60512 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq60512
  have eq60563 : x = (M.op y x) := by
    first
    | (have i₁ := eq60545
       have i₂ := eq60475
       grind)
    | exact superpose eq60475 eq60545
    | exact resolve eq60545 eq60475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60475 eq60545
  have eq60623 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq60563
       grind)
    | exact superpose eq60563 eq9
    | exact resolve eq9 eq60563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60658 : x = (M.op x y) := by
    first
    | (have i₁ := eq60623
       have i₂ := eq60563
       grind)
    | exact superpose eq60563 eq60623
    | exact resolve eq60623 eq60563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60623
  have eq60715 : x ≠ x ∨ x = y ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq60658
       grind)
    | exact superpose eq60658 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq60658
       grind)
    | exact resolve eq13 eq60658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60730 : x = y ∨ (k x y) = (M.op y x) := by grind
  clear eq60715
  have eq60752 : x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq60730
       have i₂ := eq60563
       grind)
    | exact superpose eq60563 eq60730
    | exact resolve eq60730 eq60563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60563 eq60730
  have eq60804 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2837 x y
       have i₂ := eq60752
       grind)
    | exact superpose eq60752 eq2837
    | (have j0 := eq2837 x y
       grind)
    | exact resolve eq2837 eq60752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837 eq60752
  have eq60845 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq60804
  have eq82335 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq60845
       grind)
    | exact superpose eq60845 eq16
    | exact resolve eq16 eq60845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60845
  have eq82365 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq82335
       have i₂ := eq60658
       grind)
    | exact superpose eq60658 eq82335
    | exact resolve eq82335 eq60658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60658 eq82335
  have eq82366 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq82365
  have eq82371 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq82366
       grind)
    | exact superpose eq82366 eq10
    | exact resolve eq10 eq82366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82366
  have eq82459 : x = y ∨ x = y := by
    first
    | (have i₁ := eq82371
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq82371
    | exact resolve eq82371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82371
  have eq82460 : x = y := by grind
  clear eq82459
  have eq82463 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82460
       grind)
    | exact superpose eq82460 eq16
    | exact resolve eq16 eq82460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82460
  have eq82618 : False := by grind
  exact eq82618

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pyx_Equation335 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law335 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq46 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X0 X1)
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq18
    | exact resolve eq18 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1)
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq113
    | exact resolve eq113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq111
    | exact resolve eq111 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq111
  have eq117 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq110
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq359 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq361 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
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
  clear eq19
  have eq771 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq359 x y
       grind)
    | exact superpose eq359 eq16
    | (have j1 := eq359 x y
       grind)
    | exact resolve eq16 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X1)
       have i₂ := eq359 X1 X0
       grind)
    | exact superpose eq359 eq9
    | (have j1 := eq359 X1 X0
       grind)
    | exact resolve eq9 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq3130 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq361
    | exact resolve eq361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq3187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3130 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3130
    | (have j0 := eq3130 X0 X1
       grind)
    | exact resolve eq3130 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130
  have eq17055 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq771
       have i₂ := eq3187 y x
       grind)
    | exact superpose eq3187 eq771
    | (have j1 := eq3187 (σ y) (σ x)
       grind)
    | (have r₁ := eq771
       have r₂ := eq3187 y x
       grind)
    | (have r₁ := eq771
       have r₂ := eq3187 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq771
       have r₂ := eq3187 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq771 eq3187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq3187
  have eq17056 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq17055
  have eq18392 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17056
       grind)
    | exact superpose eq17056 eq16
    | exact resolve eq16 eq17056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17056
  have eq18393 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq18392
       have r₂ := eq23 x
       grind)
    | exact resolve eq18392 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18392
  have eq18394 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq18393
       grind)
    | exact superpose eq18393 eq9
    | exact resolve eq9 eq18393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18395 : x ≠ x ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18393
       grind)
    | exact superpose eq18393 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18393
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18393
       grind)
    | exact resolve eq13 eq18393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18408 : (σ x) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18395
  have eq18419 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq18393
       have i₂ := eq18394
       grind)
    | exact superpose eq18394 eq18393
    | exact resolve eq18393 eq18394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18394
  have eq18436 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq18419
  have eq18446 : (M.op y x) = (M.op x (M.op x (M.op y x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq114 x y
       have i₂ := eq18436
       grind)
    | exact superpose eq18436 eq114
    | exact resolve eq114 eq18436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18436
  have eq18458 : (M.op y x) = (M.op (M.op y x) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq18446
       have i₂ := eq9 (M.op y x) x
       grind)
    | exact superpose eq9 eq18446
    | exact resolve eq18446 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18446
  have eq23152 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq776 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq776
    | (have j0 := eq776 (τ X0) (τ X1)
       grind)
    | exact resolve eq776 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq23257 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23152 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq23152
    | (have j0 := eq23152 X0 X1
       grind)
    | exact resolve eq23152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23152
  have eq23292 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op X1 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23257 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23257
    | (have j0 := eq23257 X0 X1
       grind)
    | exact resolve eq23257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23257
  have eq23318 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23292 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23292
    | (have j0 := eq23292 X0 X1
       grind)
    | exact resolve eq23292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23292
  have eq23341 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = (M.op X1 (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23318 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23318
    | (have j0 := eq23318 X0 X1
       grind)
    | exact resolve eq23318 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23318
  have eq23363 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23341 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23341
    | (have j0 := eq23341 X0 X1
       grind)
    | exact resolve eq23341 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23341
  have eq23384 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23363 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq23363
    | (have j0 := eq23363 X0 X1
       grind)
    | exact resolve eq23363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23363
  have eq23393 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (k X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23384 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23384
    | (have j0 := eq23384 X0 X1
       grind)
    | exact resolve eq23384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23384
  have eq65173 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq18458
       have i₂ := eq18393
       grind)
    | exact superpose eq18393 eq18458
    | exact resolve eq18458 eq18393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18393 eq18458
  have eq65189 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq65173
  have eq65204 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq65189
       grind)
    | exact superpose eq65189 eq9
    | exact resolve eq9 eq65189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65260 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65189
       have i₂ := eq65204
       grind)
    | exact superpose eq65204 eq65189
    | exact resolve eq65189 eq65204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65204
  have eq65298 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq65260
  have eq65323 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq65298
       grind)
    | exact superpose eq65298 eq9
    | exact resolve eq9 eq65298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65298
  have eq65349 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65323
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq65323
    | exact resolve eq65323 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65323
  have eq65366 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65189
       have i₂ := eq65349
       grind)
    | exact superpose eq65349 eq65189
    | exact resolve eq65189 eq65349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65189 eq65349
  have eq65396 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq65366
  have eq65431 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq65396
       grind)
    | exact superpose eq65396 eq10
    | exact resolve eq10 eq65396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65396
  have eq65507 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65431
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65431
    | exact resolve eq65431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65431
  have eq65509 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65507
       grind)
    | exact superpose eq65507 eq16
    | exact resolve eq16 eq65507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65507
  have eq65562 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq65509
       have r₂ := eq23 x
       grind)
    | exact resolve eq65509 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65509
  have eq65579 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq65562
       grind)
    | exact superpose eq65562 eq10
    | exact resolve eq10 eq65562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65562
  have eq65667 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65579
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65579
    | exact resolve eq65579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65579
  have eq65668 : x = (M.op x x) := by grind
  clear eq65667
  have eq101337 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq18408
       grind)
    | exact superpose eq18408 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18408
       grind)
    | exact resolve eq13 eq18408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18408
  have eq101357 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ x = y := by grind
  clear eq101337
  have eq101358 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ x = y := by grind
  clear eq101357
  have eq101386 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq101358
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq101358
    | exact resolve eq101358 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101358
  have eq101409 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq101386
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq101386
    | exact resolve eq101386 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101386
  have eq101426 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq101409
       have i₂ := eq65668
       grind)
    | exact superpose eq65668 eq101409
    | exact resolve eq101409 eq65668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101409
  have eq101439 : x = (k y x) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq101426
       have i₂ := eq65668
       grind)
    | exact superpose eq65668 eq101426
    | exact resolve eq101426 eq65668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101426
  have eq101501 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq776 y x
       have i₂ := eq101439
       grind)
    | exact superpose eq101439 eq776
    | (have j0 := eq776 y x
       grind)
    | exact resolve eq776 eq101439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101439
  have eq101550 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq101501
  have eq101563 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq101550
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq101550
    | exact resolve eq101550 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101550
  have eq101565 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq101563
       have i₂ := eq65668
       grind)
    | exact superpose eq65668 eq101563
    | exact resolve eq101563 eq65668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101563
  have eq101566 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq101565
  have eq115045 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq101566
       grind)
    | exact superpose eq101566 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq101566
       grind)
    | exact resolve eq13 eq101566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101566
  have eq115065 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq115045
  have eq115066 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq115065
  have eq115092 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq115066
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq115066
    | exact resolve eq115066 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115066
  have eq115110 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq115092
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq115092
    | exact resolve eq115092 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115092
  have eq115124 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq115110
       have i₂ := eq65668
       grind)
    | exact superpose eq65668 eq115110
    | exact resolve eq115110 eq65668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115110
  have eq115125 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq115124
  have eq115134 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq115125
       grind)
    | exact superpose eq115125 eq10
    | exact resolve eq10 eq115125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115125
  have eq115232 : x = y ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq115134
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq115134
    | exact resolve eq115134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115134
  have eq115233 : (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq115232
  have eq115268 : (k y x) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq115233
       grind)
    | exact superpose eq115233 eq10
    | exact resolve eq10 eq115233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115276 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (k y x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq29 X0 (k y x)
       have i₂ := eq115233
       grind)
    | exact superpose eq115233 eq29
    | exact resolve eq29 eq115233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115281 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (k y x) (τ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38 (k y x) X0
       have i₂ := eq115233
       grind)
    | exact superpose eq115233 eq38
    | exact resolve eq38 eq115233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115233
  have eq115362 : ∀ X0 : G, x = y ∨ (k x (τ X0)) = (k (k y x) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq115281 X0
       have i₂ := eq38 x X0
       grind)
    | exact superpose eq38 eq115281
    | exact resolve eq115281 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq115281
  have eq115367 : ∀ X0 : G, x = y ∨ (k (τ X0) x) = (k (τ X0) (k y x)) := by
    intro X0
    first
    | (have i₁ := eq115276 X0
       have i₂ := eq29 X0 x
       grind)
    | exact superpose eq29 eq115276
    | exact resolve eq115276 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq115276
  have eq115375 : x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq115268
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq115268
    | exact resolve eq115268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115268
  have eq115456 : (M.op y x) = (M.op x x) ∨ x = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq23393 y x
       have i₂ := eq115375
       grind)
    | exact superpose eq115375 eq23393
    | (have j0 := eq23393 y x
       grind)
    | exact resolve eq23393 eq115375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23393 eq115375
  have eq115471 : (M.op y x) = (M.op x x) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq115456
  have eq115503 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq115471
       have i₂ := eq65668
       grind)
    | exact superpose eq65668 eq115471
    | exact resolve eq115471 eq65668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115471
  have eq115504 : x = (M.op y x) ∨ x = y := by grind
  clear eq115503
  have eq115543 : (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq115504
       grind)
    | exact superpose eq115504 eq9
    | exact resolve eq9 eq115504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115648 : x = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq115504
       have i₂ := eq115543
       grind)
    | exact superpose eq115543 eq115504
    | exact resolve eq115504 eq115543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115504 eq115543
  have eq115674 : x = (M.op x y) ∨ x = y := by grind
  clear eq115648
  have eq115726 : x = y ∨ x = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have i₁ := eq114 y x
       have i₂ := eq115674
       grind)
    | exact superpose eq115674 eq114
    | exact resolve eq114 eq115674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115674
  have eq117162 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq115726
       grind)
    | exact superpose eq115726 eq16
    | exact resolve eq16 eq115726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115726
  have eq117217 : x = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have r₁ := eq117162
       have r₂ := eq23 x
       grind)
    | exact resolve eq117162 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117162
  have eq117557 : x = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq9 (M.op y x) (M.op y x)
       have i₂ := eq117217
       grind)
    | exact superpose eq117217 eq9
    | exact resolve eq9 eq117217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117558 : (M.op x (M.op y x)) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq18 (M.op y x) (M.op y x)
       have i₂ := eq117217
       grind)
    | exact superpose eq117217 eq18
    | exact resolve eq18 eq117217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117560 : x = (M.op x (M.op (M.op y x) x)) := by
    first
    | (have i₁ := eq114 (M.op y x) (M.op y x)
       have i₂ := eq117217
       grind)
    | exact superpose eq117217 eq114
    | exact resolve eq114 eq117217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117217
  have eq117910 : (M.op x (M.op y x)) = (M.op (M.op y x) (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq18 x (M.op y x)
       have i₂ := eq117557
       grind)
    | exact superpose eq117557 eq18
    | exact resolve eq18 eq117557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117913 : (M.op x (M.op x (M.op y x))) = (M.op (M.op (M.op y x) (M.op x (M.op y x))) x) := by
    first
    | (have i₁ := eq117 (M.op y x) x
       have i₂ := eq117557
       grind)
    | exact superpose eq117557 eq117
    | exact resolve eq117 eq117557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq117557
  have eq117943 : (M.op (M.op y x) x) = (M.op (M.op (M.op y x) (M.op x (M.op y x))) x) := by
    first
    | (have i₁ := eq117913
       have i₂ := eq9 (M.op y x) x
       grind)
    | exact superpose eq9 eq117913
    | exact resolve eq117913 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117913
  have eq117959 : (M.op (M.op x (M.op y x)) x) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq117943
       have i₂ := eq117910
       grind)
    | exact superpose eq117910 eq117943
    | exact resolve eq117943 eq117910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117910 eq117943
  have eq117968 : (M.op x (M.op y x)) = (M.op (M.op x (M.op y x)) x) := by
    first
    | (have i₁ := eq117959
       have i₂ := eq117558
       grind)
    | exact superpose eq117558 eq117959
    | exact resolve eq117959 eq117558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117558 eq117959
  have eq117974 : (M.op x (M.op y x)) = (M.op x (M.op (M.op y x) x)) := by
    first
    | (have i₁ := eq117968
       have i₂ := eq18 (M.op y x) x
       grind)
    | exact superpose eq18 eq117968
    | exact resolve eq117968 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117968
  have eq117977 : x = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq117974
       have i₂ := eq117560
       grind)
    | exact superpose eq117560 eq117974
    | exact resolve eq117974 eq117560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117560 eq117974
  have eq118020 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq114 x y
       have i₂ := eq117977
       grind)
    | exact superpose eq117977 eq114
    | exact resolve eq114 eq117977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118068 : (M.op y x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq118020
       have i₂ := eq18 y x
       grind)
    | exact superpose eq18 eq118020
    | exact resolve eq118020 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq118020
  have eq118083 : x = (M.op y x) := by
    first
    | (have i₁ := eq118068
       have i₂ := eq117977
       grind)
    | exact superpose eq117977 eq118068
    | exact resolve eq118068 eq117977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117977 eq118068
  have eq118148 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq118083
       grind)
    | exact superpose eq118083 eq9
    | exact resolve eq9 eq118083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118186 : x = (M.op x y) := by
    first
    | (have i₁ := eq118148
       have i₂ := eq118083
       grind)
    | exact superpose eq118083 eq118148
    | exact resolve eq118148 eq118083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118083 eq118148
  have eq121558 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x (τ X0)) = (k (k y x) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq115362 X0
       grind)
    | exact superpose eq115362 eq16
    | (have j1 := eq115362 X0
       grind)
    | exact resolve eq16 eq115362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115362
  have eq121654 : ∀ X0 : G, (k x (τ X0)) = (k (k y x) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq121558 X0
       grind)
    | (have r₁ := eq121558 X0
       have r₂ := eq23 x
       grind)
    | exact resolve eq121558 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121558
  have eq121708 : ∀ X0 : G, (k x X0) = (k (k y x) X0) := by
    intro X0
    first
    | (have i₁ := eq121654 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq121654
    | exact resolve eq121654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121654
  have eq126525 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k (τ X0) x) = (k (τ X0) (k y x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq115367 X0
       grind)
    | exact superpose eq115367 eq16
    | (have j1 := eq115367 X0
       grind)
    | exact resolve eq16 eq115367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115367
  have eq126637 : ∀ X0 : G, (k (τ X0) x) = (k (τ X0) (k y x)) := by
    intro X0
    first
    | (have j0 := eq126525 X0
       grind)
    | (have r₁ := eq126525 X0
       have r₂ := eq23 x
       grind)
    | exact resolve eq126525 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126525
  have eq126685 : ∀ X0 : G, (k X0 x) = (k X0 (k y x)) := by
    intro X0
    first
    | (have i₁ := eq126637 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126637
    | exact resolve eq126637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126637
  have eq126963 : (M.op (k y x) (k y x)) = (k (k y x) x) := by grind
  clear eq126685
  have eq127366 : (k x x) = (M.op (k y x) (k y x)) := by
    first
    | (have i₁ := eq126963
       have i₂ := eq121708 x
       grind)
    | exact superpose eq121708 eq126963
    | exact resolve eq126963 eq121708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121708 eq126963
  have eq127502 : (M.op x x) = (M.op (k y x) (k y x)) := by grind
  clear eq127366
  have eq127619 : x = (M.op (k y x) (k y x)) := by
    first
    | (have i₁ := eq127502
       have i₂ := eq65668
       grind)
    | exact superpose eq65668 eq127502
    | exact resolve eq127502 eq65668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127502
  have eq127871 : (σ x) = (M.op (σ x) (σ (k y x))) := by
    first
    | (have i₁ := eq116 (k y x)
       have i₂ := eq127619
       grind)
    | exact superpose eq127619 eq116
    | exact resolve eq116 eq127619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq127619
  have eq129637 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq776 y x
       have i₂ := eq127871
       grind)
    | exact superpose eq127871 eq776
    | (have j0 := eq776 y x
       grind)
    | exact resolve eq776 eq127871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq127871
  have eq129664 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq129637
  have eq137134 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq129664
       grind)
    | exact superpose eq129664 eq9
    | exact resolve eq9 eq129664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155229 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq129664
       have i₂ := eq137134
       grind)
    | exact superpose eq137134 eq129664
    | exact resolve eq129664 eq137134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129664 eq137134
  have eq155271 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq155229
  have eq155316 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq155271
       grind)
    | exact superpose eq155271 eq16
    | exact resolve eq16 eq155271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155271
  have eq155363 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq155316
       have i₂ := eq118186
       grind)
    | exact superpose eq118186 eq155316
    | exact resolve eq155316 eq118186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155316
  have eq155364 : (σ x) = (σ y) := by grind
  clear eq155363
  have eq155367 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq155364
       grind)
    | exact superpose eq155364 eq16
    | exact resolve eq16 eq155364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155364
  have eq155481 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq155367
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq155367
    | exact resolve eq155367 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq155367
  have eq155485 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq155481
       have i₂ := eq65668
       grind)
    | exact superpose eq65668 eq155481
    | exact resolve eq155481 eq65668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65668 eq155481
  have eq155487 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq155485
       have i₂ := eq118186
       grind)
    | exact superpose eq118186 eq155485
    | exact resolve eq155485 eq118186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118186 eq155485
  have eq155488 : False := by grind
  exact eq155488

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_x_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq14 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq54 X0 x X2
       have i₂ := eq14 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq54 X0 x X2
       have i₂ := eq14 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
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
  have eq232 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq55 X0 (M.op X0 X0)
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq55 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq298 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq613 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  clear eq77
  have eq630 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq613 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq636 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq630 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq630 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq630 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq3090 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq636 (M.op X0 X0) X1
       have i₂ := eq234 X0 (M.op X0 X0)
       grind)
    | exact superpose eq234 eq636
    | (have j0 := eq636 (M.op X0 X0) X1
       grind)
    | exact resolve eq636 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq3110 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3090 X0 X1
       have i₂ := eq55 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq3090 X0 X1
       have i₂ := eq55 (M.op X0 X0) x
       grind)
    | exact superpose eq55 eq3090
    | (have j0 := eq3090 X0 X1
       grind)
    | exact resolve eq3090 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3090
  have eq3111 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110
  have eq3170 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 (M.op X1 X1)
       have i₂ := eq3111 X1 X0
       grind)
    | exact superpose eq3111 eq298
    | exact resolve eq298 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq3175 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (k x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq3111 X0 sF2
       grind)
    | exact superpose eq3111 eq36
    | exact resolve eq36 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3176 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq3111 X0 sF3
       grind)
    | exact superpose eq3111 eq37
    | exact resolve eq37 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3111
  have eq3200 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3176 x
       have i₂ := eq234 x y
       grind)
    | exact superpose eq234 eq3176
    | exact resolve eq3176 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176
  have eq3201 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3175 x
       have i₂ := eq234 x x
       grind)
    | exact superpose eq234 eq3175
    | exact resolve eq3175 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175
  have eq3217 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3200
       grind)
    | exact superpose eq3200 eq16
    | exact resolve eq16 eq3200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3200
  have eq3246 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3201
       grind)
    | exact superpose eq3201 eq16
    | exact resolve eq16 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201
  have eq3464 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3170 X0 x
       have i₂ := eq234 x (τ X0)
       grind)
    | exact superpose eq234 eq3170
    | exact resolve eq3170 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq3170
  have eq3577 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3464 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3464
    | exact resolve eq3464 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3464
  have eq3940 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq3577 X0
       grind)
    | exact superpose eq3577 eq15
    | exact resolve eq15 eq3577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3577
  have eq4104 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) x
       have i₂ := eq3940 X0
       grind)
    | exact superpose eq3940 eq55
    | exact resolve eq55 eq3940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3940
  have eq35524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq35525 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq35524
    | exact resolve eq35524 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35524
  have eq35536 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq35525
       have r₂ := eq28
       grind)
    | exact resolve eq35525 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35525
  have eq35540 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq35536 eq3217
    | exact resolve eq3217 eq35536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3217 eq35536
  have eq35635 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq35540
    | exact resolve eq35540 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35540
  have eq35636 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq35635
  have eq35642 : (τ (σ y)) = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq35636 eq3246
    | exact resolve eq3246 eq35636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246 eq35636
  have eq35739 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq35642
    | exact resolve eq35642 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35642
  have eq35740 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq35739
  have eq35755 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq55 y x
       have i₂ := eq35740
       grind)
    | exact superpose eq35740 eq55
    | exact resolve eq55 eq35740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35791 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq4104 y x
       have i₂ := eq35740
       grind)
    | exact superpose eq35740 eq4104
    | exact resolve eq4104 eq35740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35740
  have eq35820 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq35791 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35791
    | (have j0 := eq35791 X0
       grind)
    | exact resolve eq35791 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35791
  have eq36100 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x
       have i₂ := eq35755 X0
       grind)
    | exact superpose eq35755 eq55
    | (have j1 := eq35755 X1
       grind)
    | exact resolve eq55 eq35755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq35755
  have eq36296 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35820
    | (have j0 := eq35820 (σ x)
       grind)
    | exact resolve eq35820 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35820
  have eq36797 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4104 x x
       have i₂ := eq36296
       grind)
    | exact superpose eq36296 eq4104
    | exact resolve eq4104 eq36296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104 eq36296
  have eq36827 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36797 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36797
    | (have j0 := eq36797 X0
       grind)
    | exact resolve eq36797 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36797
  have eq37453 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36827 eq27
    | (have j1 := eq36827 (σ x)
       grind)
    | exact resolve eq27 eq36827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq36827
  have eq37463 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq37453
  have eq37504 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq37463 eq28
    | exact resolve eq28 eq37463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq37463
  have eq38373 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq36100 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36100
  have eq38374 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq38373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38373
  have eq38410 : y = (M.op x y) := by
    first
    | (have i₁ := eq38374 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq38374
    | (have j0 := eq38374 x
       grind)
    | exact resolve eq38374 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38374
  have eq38526 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38410 eq21
    | exact resolve eq21 eq38410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq38410
  have eq38665 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq38526
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38526
    | exact resolve eq38526 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq38526
  have eq38695 : False := by grind
  exact eq38695

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq14 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq54 X0 x X2
       have i₂ := eq14 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq54 X0 x X2
       have i₂ := eq14 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
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
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq228 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq55 X0 (M.op X0 X0)
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq55 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq228 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq269 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq113 (τ X0)
       grind)
    | exact superpose eq113 eq35
    | exact resolve eq35 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq113
  have eq480 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  clear eq77
  have eq485 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq492 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq485 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq485 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq485 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq3170 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq492 (M.op X0 X0) X1
       have i₂ := eq230 X0 (M.op X0 X0)
       grind)
    | exact superpose eq230 eq492
    | (have j0 := eq492 (M.op X0 X0) X1
       grind)
    | exact resolve eq492 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq3187 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3170 X0 X1
       have i₂ := eq55 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq3170 X0 X1
       have i₂ := eq55 (M.op X0 X0) x
       grind)
    | exact superpose eq55 eq3170
    | (have j0 := eq3170 X0 X1
       grind)
    | exact resolve eq3170 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3170
  have eq3188 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq3214 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3188 (τ X0) X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq3188
    | exact resolve eq3188 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq3249 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (k x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq3188 X0 sF2
       grind)
    | exact superpose eq3188 eq36
    | exact resolve eq36 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3250 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq3188 X0 sF3
       grind)
    | exact superpose eq3188 eq37
    | exact resolve eq37 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3188
  have eq3274 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3250 x
       have i₂ := eq230 x y
       grind)
    | exact superpose eq230 eq3250
    | exact resolve eq3250 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3250
  have eq3275 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3249 x
       have i₂ := eq230 x x
       grind)
    | exact superpose eq230 eq3249
    | exact resolve eq3249 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq3249
  have eq3287 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3274
       grind)
    | exact superpose eq3274 eq16
    | exact resolve eq16 eq3274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq3316 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3275
       grind)
    | exact superpose eq3275 eq16
    | exact resolve eq16 eq3275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3275
  have eq3671 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3214 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3214
    | exact resolve eq3214 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3214
  have eq3978 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) x
       have i₂ := eq3671 X0
       grind)
    | exact superpose eq3671 eq55
    | exact resolve eq55 eq3671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671
  have eq35616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq35617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq35616
    | exact resolve eq35616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35616
  have eq35628 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq35617
       have r₂ := eq28
       grind)
    | exact resolve eq35617 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35617
  have eq35632 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq35628 eq3287
    | exact resolve eq3287 eq35628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287 eq35628
  have eq35725 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq35632
    | exact resolve eq35632 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35632
  have eq35726 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq35725
  have eq35732 : (τ (σ y)) = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq35726 eq3316
    | exact resolve eq3316 eq35726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3316 eq35726
  have eq35820 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq35732
    | exact resolve eq35732 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35732
  have eq35821 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq35820
  have eq35834 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq55 y x
       have i₂ := eq35821
       grind)
    | exact superpose eq35821 eq55
    | exact resolve eq55 eq35821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35864 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq3978 y x
       have i₂ := eq35821
       grind)
    | exact superpose eq35821 eq3978
    | exact resolve eq3978 eq35821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35821
  have eq35899 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq35864 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq35864
    | (have j0 := eq35864 X0
       grind)
    | exact resolve eq35864 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35864
  have eq36153 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x
       have i₂ := eq35834 X0
       grind)
    | exact superpose eq35834 eq55
    | (have j1 := eq35834 X1
       grind)
    | exact resolve eq55 eq35834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq35834
  have eq36247 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35899
    | (have j0 := eq35899 (σ x)
       grind)
    | exact resolve eq35899 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35899
  have eq36396 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3978 x x
       have i₂ := eq36247
       grind)
    | exact superpose eq36247 eq3978
    | exact resolve eq3978 eq36247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3978 eq36247
  have eq36430 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36396 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36396
    | (have j0 := eq36396 X0
       grind)
    | exact resolve eq36396 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36396
  have eq37452 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36430 eq27
    | (have j1 := eq36430 (σ x)
       grind)
    | exact resolve eq27 eq36430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq36430
  have eq37462 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq37452
  have eq37501 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq37462 eq28
    | exact resolve eq28 eq37462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq37462
  have eq38364 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq36153 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36153
  have eq38365 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq38364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38364
  have eq38400 : y = (M.op x y) := by
    first
    | (have i₁ := eq38365 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq38365
    | (have j0 := eq38365 x
       grind)
    | exact resolve eq38365 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38365
  have eq38514 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38400 eq21
    | exact resolve eq21 eq38400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq38400
  have eq38651 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq38514
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38514
    | exact resolve eq38514 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq38514
  have eq38680 : False := by grind
  exact eq38680

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxx_pyx_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
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
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq16 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq177 X0 x X2
       have i₂ := eq16 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq177 X0 x X2
       have i₂ := eq16 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq870 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq871 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq915 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq915 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq915 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq943 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 x
       have i₂ := eq921 X0
       grind)
    | exact superpose eq921 eq178
    | exact resolve eq178 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq995 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq943 (σ X1) X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq943
    | exact resolve eq943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3473 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq870
       grind)
    | exact superpose eq870 eq40
    | exact resolve eq40 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq3474 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3473
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3473
    | exact resolve eq3473 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3473
  have eq3476 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq3474
    | exact resolve eq3474 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq3478 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq3476
       have i₂ := eq921 y
       grind)
    | exact superpose eq921 eq3476
    | exact resolve eq3476 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq159048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq3478 eq871
    | exact resolve eq871 eq3478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159057 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq159048
       have r₂ := eq27
       grind)
    | exact resolve eq159048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159048
  have eq159064 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq159057
       have i₂ := eq921 sF3
       grind)
    | exact superpose eq921 eq159057
    | exact resolve eq159057 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159057
  have eq159070 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq159064 eq12
    | (have j0 := eq12 x (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq159064
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq159064
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq159064
       grind)
    | exact resolve eq12 eq159064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159064
  have eq159091 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq159070
       have r₂ := eq26
       grind)
    | exact resolve eq159070 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159070
  have eq159101 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq159091
       have i₂ := eq921 sF3
       grind)
    | exact superpose eq921 eq159091
    | exact resolve eq159091 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159091
  have eq159102 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq159101
  have eq159106 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq3478 eq159102
    | exact resolve eq159102 eq3478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3478 eq159102
  have eq159108 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq159106
       have r₂ := eq27
       grind)
    | exact resolve eq159106 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159106
  have eq159114 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq159108 eq152
    | exact resolve eq152 eq159108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159108
  have eq159462 : y = (k y y) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq31 eq159114
    | exact resolve eq159114 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159114
  have eq159463 : (M.op x y) = (M.op y x) ∨ y = (k y y) := by grind
  clear eq159462
  have eq159525 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq159463
       grind)
    | exact superpose eq159463 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq159463
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq159463
       grind)
    | exact resolve eq12 eq159463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159463
  have eq159546 : y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have r₁ := eq159525
       have r₂ := eq18
       grind)
    | exact resolve eq159525 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159525
  have eq159556 : y = (k y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq159546
       have i₂ := eq921 y
       grind)
    | exact superpose eq921 eq159546
    | exact resolve eq159546 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159546
  have eq159557 : (M.op x y) = (k x y) ∨ y = (k y y) := by grind
  clear eq159556
  have eq159565 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq159557
       grind)
    | exact superpose eq159557 eq40
    | exact resolve eq40 eq159557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq159557
  have eq159567 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq159565
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq159565
    | exact resolve eq159565 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq159565
  have eq159571 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq159567
    | exact resolve eq159567 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159567
  have eq159576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq159571 eq871
    | exact resolve eq871 eq159571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq159585 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq159576
       have r₂ := eq27
       grind)
    | exact resolve eq159576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159576
  have eq159592 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq159585
       have i₂ := eq921 sF3
       grind)
    | exact superpose eq921 eq159585
    | exact resolve eq159585 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159585
  have eq231738 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq159592 eq12
    | (have j0 := eq12 x (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq159592
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq159592
       grind)
    | exact resolve eq12 eq159592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159592
  have eq231759 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq231738
       have r₂ := eq26
       grind)
    | exact resolve eq231738 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231738
  have eq231769 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq231759
       have i₂ := eq921 sF3
       grind)
    | exact superpose eq921 eq231759
    | exact resolve eq231759 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq231759
  have eq231770 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by grind
  clear eq231769
  have eq231774 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq159571 eq231770
    | exact resolve eq231770 eq159571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159571 eq231770
  have eq231776 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq231774
       have r₂ := eq27
       grind)
    | exact resolve eq231774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231774
  have eq231783 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq231776 eq152
    | exact resolve eq152 eq231776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq231776
  have eq232161 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq231783
    | exact resolve eq231783 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq231783
  have eq232162 : y = (k y y) := by grind
  clear eq232161
  have eq232240 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq943 y x
       have i₂ := eq232162
       grind)
    | exact superpose eq232162 eq943
    | exact resolve eq943 eq232162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq232258 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq995 y x
       have i₂ := eq232162
       grind)
    | exact superpose eq232162 eq995
    | exact resolve eq995 eq232162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq232162
  have eq232587 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq232258 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq232258
    | (have j0 := eq232258 X0
       grind)
    | exact resolve eq232258 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232258
  have eq232758 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq232240 x
       grind)
    | exact superpose eq232240 eq18
    | (have j1 := eq232240 x
       grind)
    | exact resolve eq18 eq232240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq232240
  have eq232892 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq232758
       grind)
    | exact superpose eq232758 eq24
    | exact resolve eq24 eq232758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq232758
  have eq233116 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq232892 eq20
    | exact resolve eq20 eq232892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq232892
  have eq234043 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq232587 eq26
    | (have j1 := eq232587 (σ x)
       grind)
    | exact resolve eq26 eq232587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq232587
  have eq234176 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq234043 eq27
    | exact resolve eq27 eq234043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq234043
  have eq234198 : False := by grind
  exact eq234198

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxx_y_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq14 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 X0 x X2
       have i₂ := eq14 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq53 X0 x X2
       have i₂ := eq14 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq76 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq233 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq54 X0 (M.op X0 X0)
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq54 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq300 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq581 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq585 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq581 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq591 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq585 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq585 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq585 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq2935 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq591 (M.op X0 X0) X1
       have i₂ := eq235 X0 (M.op X0 X0)
       grind)
    | exact superpose eq235 eq591
    | (have j0 := eq591 (M.op X0 X0) X1
       grind)
    | exact resolve eq591 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq2952 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2935 X0 X1
       have i₂ := eq54 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq2935 X0 X1
       have i₂ := eq54 (M.op X0 X0) x
       grind)
    | exact superpose eq54 eq2935
    | (have j0 := eq2935 X0 X1
       grind)
    | exact resolve eq2935 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935
  have eq2953 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq2952 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952
  have eq3014 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 (M.op X1 X1)
       have i₂ := eq2953 X1 X0
       grind)
    | exact superpose eq2953 eq300
    | exact resolve eq300 eq2953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq3018 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq2953 X0 sF1
       grind)
    | exact superpose eq2953 eq37
    | exact resolve eq37 eq2953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq3020 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq2953 X0 sF3
       grind)
    | exact superpose eq2953 eq36
    | exact resolve eq36 eq2953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2953
  have eq3044 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3020 x
       have i₂ := eq235 x y
       grind)
    | exact superpose eq235 eq3020
    | exact resolve eq3020 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020
  have eq3046 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq3018 x
       have i₂ := eq235 x sF0
       grind)
    | exact superpose eq235 eq3018
    | exact resolve eq3018 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018
  have eq3056 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3044
       grind)
    | exact superpose eq3044 eq16
    | exact resolve eq16 eq3044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3112 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3046 eq16
    | exact resolve eq16 eq3046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046
  have eq3676 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3014 X0 x
       have i₂ := eq235 x (τ X0)
       grind)
    | exact superpose eq235 eq3014
    | exact resolve eq3014 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq3014
  have eq3790 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3676 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3676
    | exact resolve eq3676 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3676
  have eq4269 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq3790 X0
       grind)
    | exact superpose eq3790 eq15
    | exact resolve eq15 eq3790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq4507 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) x
       have i₂ := eq4269 X0
       grind)
    | exact superpose eq4269 eq54
    | exact resolve eq54 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5543 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq4269 X1
       grind)
    | exact superpose eq4269 eq582
    | (have j0 := eq582 X0 X1
       grind)
    | exact resolve eq582 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq4269
  have eq14437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq14437
    | exact resolve eq14437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14437
  have eq14449 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq14438
       have r₂ := eq27
       grind)
    | exact resolve eq14438 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14438
  have eq14453 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq14449
    | exact resolve eq14449 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14449
  have eq14455 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq14453 eq3056
    | exact resolve eq3056 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14453
  have eq14484 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq14455
    | exact resolve eq14455 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14455
  have eq14485 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14484
  have eq14490 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq54 y x
       have i₂ := eq14485
       grind)
    | exact superpose eq14485 eq54
    | exact resolve eq54 eq14485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14485
  have eq14542 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14490 x
       grind)
    | exact superpose eq14490 eq18
    | (have j1 := eq14490 x
       grind)
    | exact resolve eq18 eq14490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14490
  have eq14547 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14542
  have eq14733 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14547 eq77
    | (have r₁ := eq77
       have r₂ := eq14547
       grind)
    | exact resolve eq77 eq14547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq14735 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14547 eq27
    | exact resolve eq27 eq14547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14547
  have eq14736 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14733
  have eq15329 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14736 eq117
    | exact resolve eq117 eq14736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq14736
  have eq15342 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq15329
  have eq15353 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15342
       have r₂ := eq14735
       grind)
    | exact resolve eq15342 eq14735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14735 eq15342
  have eq15361 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15353 eq3056
    | exact resolve eq3056 eq15353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056 eq15353
  have eq15390 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq15361
    | exact resolve eq15361 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15361
  have eq15391 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq15390
  have eq15396 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq54 y x
       have i₂ := eq15391
       grind)
    | exact superpose eq15391 eq54
    | exact resolve eq54 eq15391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq15391
  have eq15449 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15396 x
       grind)
    | exact superpose eq15396 eq18
    | (have j1 := eq15396 x
       grind)
    | exact resolve eq18 eq15396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq15396
  have eq15454 : y = (M.op x y) := by grind
  clear eq15449
  have eq15466 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq15454 eq20
    | exact resolve eq20 eq15454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq15472 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq15454 eq76
    | (have r₁ := eq76
       have r₂ := eq15454
       grind)
    | exact resolve eq76 eq15454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq15523 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq15472
  have eq15573 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15466
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15466
    | exact resolve eq15466 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15466
  have eq15621 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq15573 eq26
    | exact resolve eq26 eq15573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq15864 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5543 x y
       have i₂ := eq15523
       grind)
    | exact superpose eq15523 eq5543
    | (have j0 := eq5543 x y
       grind)
    | exact resolve eq5543 eq15523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5543 eq15523
  have eq15867 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq15864
  have eq15870 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15867
       have i₂ := eq3044
       grind)
    | exact superpose eq3044 eq15867
    | exact resolve eq15867 eq3044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044 eq15867
  have eq15880 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15573 eq15870
    | exact resolve eq15870 eq15573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15870
  have eq15888 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15880
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15880
    | exact resolve eq15880 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15880
  have eq15896 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15573 eq15888
    | exact resolve eq15888 eq15573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15888
  have eq15899 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15896
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15896
    | exact resolve eq15896 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896
  have eq15900 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15573 eq15899
    | exact resolve eq15899 eq15573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15899
  have eq15901 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15900
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15900
    | exact resolve eq15900 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15900
  have eq15902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15621 eq15901
    | exact resolve eq15901 eq15621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15901
  have eq15903 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq15902
       have r₂ := eq27
       grind)
    | exact resolve eq15902 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15902
  have eq15955 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15903 eq3112
    | exact resolve eq3112 eq15903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112 eq15903
  have eq15984 : (τ (σ (M.op x y))) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15454 eq15955
    | exact resolve eq15955 eq15454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955
  have eq15989 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq15984
    | exact resolve eq15984 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15984
  have eq15991 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15454 eq15989
    | exact resolve eq15989 eq15454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15454 eq15989
  have eq15992 : y = (M.op y y) := by grind
  clear eq15991
  have eq16010 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4507 y x
       have i₂ := eq15992
       grind)
    | exact superpose eq15992 eq4507
    | exact resolve eq4507 eq15992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4507 eq15992
  have eq16018 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16010 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16010
    | (have j0 := eq16010 X0
       grind)
    | exact resolve eq16010 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16010
  have eq16025 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq15573 eq16018
    | exact resolve eq16018 eq15573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15573 eq16018
  have eq16110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16025 eq15621
    | exact resolve eq15621 eq16025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15621 eq16025
  have eq16116 : False := by grind
  exact eq16116

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_x_pyx_Equation3499 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3499 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X2) X0)) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq174 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X3 (M.op (M.op X4 X4) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X3 X4
       have i₂ := eq16 X2 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X3 X4 X2
       have i₂ := eq16 X2 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X1 X1) X0) X2 x
       have i₂ := eq16 X0 (M.op x x) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq179 X0 x X2
       have i₂ := eq16 X0 (M.op (M.op x x) X0) x
       grind)
    | (have i₁ := eq179 X0 x X2
       have i₂ := eq16 (M.op (M.op x x) X0) x X2
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq184 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X3 (M.op X0 (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq181 X0 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq181
    | exact resolve eq181 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq196 : ∀ X0 X1 X2 X3 : G, (M.op X0 (k (M.op X1 X1) X2)) = (M.op X3 (M.op X0 (k (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184 X0 X0 X1 X3
       have i₂ := eq192 X0 X1
       grind)
    | exact superpose eq192 eq184
    | exact resolve eq184 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq320 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq377 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq411 : ∀ X0 X1 : G, (k (τ X1) (k X0 y)) = (τ (k X1 (k (σ X0) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq320 X1 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq320
    | exact resolve eq320 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (k (τ X1) (k X0 (M.op x y))) = (τ (k X1 (k (σ X0) (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq41 eq320
    | exact resolve eq320 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X3) = (k (M.op X0 (M.op (M.op X1 X1) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq192
    | exact resolve eq192 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (k (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq192 X0 X1
       grind)
    | exact superpose eq192 eq16
    | exact resolve eq16 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X0) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X0 X0) X1
       have i₂ := eq192 X0 (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq192 eq16
    | exact resolve eq16 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1 (M.op X0 X0)
       have i₂ := eq192 X0 (M.op X1 X1)
       grind)
    | exact superpose eq192 eq181
    | exact resolve eq181 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 X0) (k (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq560 X0 X1 X2
       have i₂ := eq192 X1 X2
       grind)
    | exact superpose eq192 eq560
    | exact resolve eq560 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq569 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (k (M.op X1 X1) X2)) X3) = (k (M.op X0 (k (M.op X1 X1) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq548 X0 X0 X1 X3
       have i₂ := eq192 X0 X1
       grind)
    | exact superpose eq192 eq548
    | exact resolve eq548 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1084 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1112 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1148 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1116 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1116
    | (have j0 := eq1116 (σ X0)
       grind)
    | exact resolve eq1116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1154 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1084 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1084
    | (have j0 := eq1084 X0
       have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1084 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1154 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1181 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1171 X0
       have j1 := eq1116 X0
       grind)
    | (have r₁ := eq1171 X0
       have r₂ := eq1116 X0
       grind)
    | exact resolve eq1171 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1196 : (σ y) = (k (σ y) (σ (k y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq36 (k y y)
       have i₂ := eq1181 y
       grind)
    | exact superpose eq1181 eq36
    | (have j1 := eq1181 y
       grind)
    | exact resolve eq36 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1181
  have eq1205 : (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1196
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq1196
    | exact resolve eq1196 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1215 : (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1205
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1205
    | exact resolve eq1205 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1930 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X3) X2) (M.op (M.op X3 X3) X2)) = (M.op X4 (M.op X0 (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X4 x
       have i₂ := eq174 (M.op x x) X3 X2 X0 X1
       grind)
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X4 x
       have i₂ := eq174 X0 X1 X2 (M.op x x) X3
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1933 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X3) X2) (M.op (M.op X3 X3) X2)) = (M.op X4 (M.op X0 (k (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1930 X0 X1 X2 X3 X4
       have i₂ := eq192 X1 X2
       grind)
    | exact superpose eq192 eq1930
    | exact resolve eq1930 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq1997 : ∀ X0 X1 X2 X4 : G, (M.op X2 X2) = (M.op X4 (M.op X0 (k (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1933 X0 X1 X2 x X4
       have i₂ := eq16 X2 (M.op (M.op x x) X2) x
       grind)
    | (have i₁ := eq1933 X0 X1 X2 x X4
       have i₂ := eq16 (M.op (M.op x x) X2) X1 X2
       grind)
    | exact superpose eq16 eq1933
    | exact resolve eq1933 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933
  have eq2092 : ∀ X0 X1 X2 X3 X4 : G, (k X0 X0) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X3) X4)) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 X2 X3 X4 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2190 : ∀ X0 X1 X3 X4 X5 X6 X7 : G, (M.op X1 (M.op X0 X0)) = (M.op X6 (M.op (M.op X7 X7) (M.op (M.op X3 (M.op (M.op X4 X4) X5)) X0))) := by
    intro X0 X1 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq174 X1 x (M.op (M.op X3 (M.op (M.op X4 X4) X5)) X0) X6 X7
       have i₂ := eq176 X3 X4 X5 X0 (M.op x x)
       grind)
    | exact superpose eq176 eq174
    | exact resolve eq174 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq2195 : ∀ X0 X1 X2 X3 X4 : G, (k X0 X0) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X3) X4)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq2092 X0 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq2198 : ∀ X0 X1 X3 X4 X5 X6 X7 : G, (M.op X1 (M.op X0 X0)) = (M.op X6 (k (M.op X7 X7) (M.op (M.op X3 (M.op (M.op X4 X4) X5)) X0))) := by
    intro X0 X1 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq2190 X0 X1 X3 X4 X5 X6 X7
       have i₂ := eq192 X7 (M.op (M.op X3 (M.op (M.op X4 X4) X5)) X0)
       grind)
    | exact superpose eq192 eq2190
    | exact resolve eq2190 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190
  have eq2269 : ∀ X0 X1 X2 X3 X4 : G, (k X0 X0) = (M.op X1 (M.op (M.op X2 (k (M.op X3 X3) X4)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2195 X0 X1 X2 X3 X4
       have i₂ := eq192 X3 X4
       grind)
    | exact superpose eq192 eq2195
    | (have j0 := eq2195 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq2195 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2274 : ∀ X0 X1 X3 X4 X5 X6 X7 : G, (M.op X1 (M.op X0 X0)) = (M.op X6 (k (M.op X7 X7) (M.op (M.op X3 (k (M.op X4 X4) X5)) X0))) := by
    intro X0 X1 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq2198 X0 X1 X3 X4 X5 X6 X7
       have i₂ := eq192 X4 X5
       grind)
    | exact superpose eq192 eq2198
    | exact resolve eq2198 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2325 : ∀ X0 X1 X2 X3 X4 : G, (k X0 X0) = (M.op X1 (k (M.op X2 (k (M.op X3 X3) X4)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2269 X0 X1 X2 X3 X4
       have i₂ := eq569 X2 X3 X4 X0
       grind)
    | exact superpose eq569 eq2269
    | (have j0 := eq2269 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq2269 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2329 : ∀ X0 X1 X3 X4 X5 X6 X7 : G, (M.op X1 (M.op X0 X0)) = (M.op X6 (k (M.op X7 X7) (k (M.op X3 (k (M.op X4 X4) X5)) X0))) := by
    intro X0 X1 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq2274 X0 X1 X3 X4 X5 X6 X7
       have i₂ := eq569 X3 X4 X5 X0
       grind)
    | exact superpose eq569 eq2274
    | exact resolve eq2274 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq2274
  have eq2490 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X0)) = (M.op (M.op X1 (k (M.op X2 X2) X0)) (M.op X1 (k (M.op X2 X2) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 x x x (M.op X1 (k (M.op X2 X2) X0)) X3
       have i₂ := eq1997 X1 X2 X0 (M.op x (M.op (M.op x x) x))
       grind)
    | exact superpose eq1997 eq176
    | exact resolve eq176 eq1997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq1997
  have eq2494 : ∀ X0 X1 X2 X3 : G, (M.op X1 (k (M.op X2 X2) X0)) = (M.op X3 (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2490 X0 X1 X2 X3
       have i₂ := eq196 X1 X2 X0 (M.op X1 (k (M.op X2 X2) X0))
       grind)
    | exact superpose eq196 eq2490
    | exact resolve eq2490 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq2490
  have eq7930 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq39
    | exact resolve eq39 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq7931 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7930
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7930
    | exact resolve eq7930 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7930
  have eq7935 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq7931
    | exact resolve eq7931 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7931
  have eq17265 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1148 (M.op X0 X0)
       have i₂ := eq561 X0 X0
       grind)
    | exact superpose eq561 eq1148
    | (have j0 := eq1148 (M.op X0 X0)
       grind)
    | exact resolve eq1148 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq17301 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq17265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17265
  have eq17456 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq181 (σ (M.op X0 X0)) x
       have i₂ := eq17301 X0
       grind)
    | exact superpose eq17301 eq181
    | exact resolve eq181 eq17301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17458 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq192 (σ (M.op X0 X0)) X1
       have i₂ := eq17301 X0
       grind)
    | exact superpose eq17301 eq192
    | exact resolve eq192 eq17301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17461 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ (M.op X0 X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq561 (σ (M.op X0 X0)) X1
       have i₂ := eq17301 X0
       grind)
    | exact superpose eq17301 eq561
    | exact resolve eq561 eq17301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17462 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (M.op X1 X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq561 X0 (σ (M.op X0 X0))
       have i₂ := eq17301 X0
       grind)
    | exact superpose eq17301 eq561
    | exact resolve eq561 eq17301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17465 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (M.op X2 X2) (k (σ (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq562 X2 (σ (M.op X0 X0)) X1
       have i₂ := eq17301 X0
       grind)
    | exact superpose eq17301 eq562
    | exact resolve eq562 eq17301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17301
  have eq17990 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (M.op X1 X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq377 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq17461 X1 X0
       grind)
    | exact superpose eq17461 eq377
    | exact resolve eq377 eq17461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq17461
  have eq18591 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ (M.op X1 X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq320 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq17462 X0 X1
       grind)
    | exact superpose eq17462 eq320
    | exact resolve eq320 eq17462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq18594 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (M.op X1 X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18591 X0 X1
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq18591
    | exact resolve eq18591 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18591
  have eq18688 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1084 (τ (M.op X0 X0))
       have i₂ := eq18594 (τ (M.op X0 X0)) X0
       grind)
    | exact superpose eq18594 eq1084
    | (have j0 := eq1084 (τ (M.op X0 X0))
       grind)
    | exact resolve eq1084 eq18594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084 eq18594
  have eq18690 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq18688 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18688
  have eq19415 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq555 x (τ (M.op X0 X0)) X1
       have i₂ := eq17990 X0 x
       grind)
    | exact superpose eq17990 eq555
    | exact resolve eq555 eq17990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17990
  have eq19424 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19415 X0 X1
       have i₂ := eq18690 X0
       grind)
    | exact superpose eq18690 eq19415
    | exact resolve eq19415 eq18690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18690 eq19415
  have eq19524 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (τ (M.op X0 X0)) (k (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq562 (τ (M.op X0 X0)) X2 X1
       have i₂ := eq19424 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq19424 eq562
    | exact resolve eq562 eq19424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq19424
  have eq21783 : ∀ X0 X1 : G, (τ (M.op (σ y) (σ y))) = (k (τ (M.op X0 X0)) (k (M.op X1 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq411 (M.op X0 X0) (M.op x x)
       have i₂ := eq17465 X0 sF3 x
       grind)
    | exact superpose eq17465 eq411
    | exact resolve eq411 eq17465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq21784 : ∀ X0 X1 : G, (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (τ (M.op X0 X0)) (k (M.op X1 X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq412 (M.op X0 X0) (M.op x x)
       have i₂ := eq17465 X0 sF1 x
       grind)
    | exact superpose eq17465 eq412
    | exact resolve eq412 eq17465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq17465
  have eq21791 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq21784 x x
       have i₂ := eq19524 x sF0 x
       grind)
    | exact superpose eq19524 eq21784
    | exact resolve eq21784 eq19524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21784
  have eq21792 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq21783 x x
       have i₂ := eq19524 x y x
       grind)
    | exact superpose eq19524 eq21783
    | exact resolve eq21783 eq19524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19524 eq21783
  have eq22018 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq21792 eq14
    | exact resolve eq14 eq21792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21792
  have eq22269 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22018
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq22018
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq22018 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22359 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq22269
  have eq22414 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22359
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq22359
    | exact resolve eq22359 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22359
  have eq22433 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22414
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22414
    | exact resolve eq22414 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22414
  have eq22437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq7935 eq1113
    | exact resolve eq1113 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7935
  have eq22444 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq22437
       have r₂ := eq27
       grind)
    | exact resolve eq22437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22437
  have eq22450 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22433 eq22444
    | exact resolve eq22444 eq22433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22444
  have eq22452 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22433 eq22450
    | exact resolve eq22450 eq22433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22433 eq22450
  have eq22607 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22452 eq152
    | exact resolve eq152 eq22452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq22452
  have eq22625 : y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq22607
    | exact resolve eq22607 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22607
  have eq22631 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq1116 y
       grind)
    | (have r₁ := eq22625
       have r₂ := eq1116 y
       grind)
    | exact resolve eq22625 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq22625
  have eq22637 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22631 eq1215
    | exact resolve eq1215 eq22631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq22638 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22631 eq115
    | exact resolve eq115 eq22631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22631
  have eq22648 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq22637
  have eq22656 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq22638
    | exact resolve eq22638 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22638
  have eq22674 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22648 eq141
    | exact resolve eq141 eq22648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq22648
  have eq22677 : y = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq22674
    | exact resolve eq22674 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq22674
  have eq22684 : y = (k y x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq22677
       have r₂ := eq12 y y
       grind)
    | (have r₁ := eq22677
       have r₂ := eq12 y x
       grind)
    | exact resolve eq22677 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22677
  have eq22690 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1112
       have i₂ := eq22684
       grind)
    | exact superpose eq22684 eq1112
    | exact resolve eq1112 eq22684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq22684
  have eq22695 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq22690
  have eq22815 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 y x
       have i₂ := eq22695
       grind)
    | exact superpose eq22695 eq181
    | exact resolve eq181 eq22695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22695
  have eq24144 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22815 x
       grind)
    | exact superpose eq22815 eq18
    | (have j1 := eq22815 x
       grind)
    | exact resolve eq18 eq22815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22815
  have eq24150 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq24144
  have eq24177 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq192 y x
       have i₂ := eq24150
       grind)
    | exact superpose eq24150 eq192
    | exact resolve eq192 eq24150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24190 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17458 y x
       have i₂ := eq24150
       grind)
    | exact superpose eq24150 eq17458
    | exact resolve eq17458 eq24150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24150
  have eq24228 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24190 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24190
    | (have j0 := eq24190 X0
       grind)
    | exact resolve eq24190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24190
  have eq25702 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24177 y
       grind)
    | exact superpose eq24177 eq18
    | (have j1 := eq24177 y
       grind)
    | exact resolve eq18 eq24177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24177
  have eq25933 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq25702
       grind)
    | exact superpose eq25702 eq40
    | exact resolve eq40 eq25702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25702
  have eq25934 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25933
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25933
    | exact resolve eq25933 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25933
  have eq25938 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq25934
    | exact resolve eq25934 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25934
  have eq26524 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24228 eq26
    | (have j1 := eq24228 (σ y)
       grind)
    | exact resolve eq26 eq24228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24228
  have eq26707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25938 eq26524
    | exact resolve eq26524 eq25938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25938 eq26524
  have eq26744 : y = (M.op x y) := by
    first
    | (have r₁ := eq26707
       have r₂ := eq27
       grind)
    | exact resolve eq26707 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26707
  have eq26755 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26744
       grind)
    | exact superpose eq26744 eq18
    | exact resolve eq18 eq26744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq26756 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq26744
       grind)
    | exact superpose eq26744 eq24
    | exact resolve eq24 eq26744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26758 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq26744
       grind)
    | exact superpose eq26744 eq40
    | exact resolve eq40 eq26744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq26778 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq22018
       have i₂ := eq26744
       grind)
    | exact superpose eq26744 eq22018
    | exact resolve eq22018 eq26744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22018
  have eq26796 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26756 eq20
    | exact resolve eq20 eq26756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27063 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26796 eq21791
    | exact resolve eq21791 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21791
  have eq27220 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq26778
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq26778
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq26778 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27312 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq27220
  have eq27380 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41 eq27312
    | exact resolve eq27312 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27312
  have eq27435 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26796 eq27380
    | exact resolve eq27380 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27380
  have eq27460 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq27435
    | exact resolve eq27435 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27435
  have eq27466 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26796 eq27460
    | exact resolve eq27460 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27460
  have eq33811 : (τ (k (σ y) (σ y))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27466 eq27063
    | exact resolve eq27063 eq27466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27063 eq27466
  have eq33907 : (k y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq115 eq33811
    | exact resolve eq33811 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq33811
  have eq33925 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq33907
       have i₂ := eq26744
       grind)
    | exact superpose eq26744 eq33907
    | exact resolve eq33907 eq26744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33907
  have eq33928 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq33925
       have r₂ := eq13 (M.op x y) x
       grind)
    | exact resolve eq33925 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33925
  have eq33934 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq33928 eq26778
    | exact resolve eq26778 eq33928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26778
  have eq33966 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op X0 (k (k (M.op x y) (M.op x y)) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq33928 eq2494
    | exact resolve eq2494 eq33928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq33969 : ∀ X0 : G, (k (σ (k (M.op x y) (M.op x y))) X0) = (M.op (σ (k (M.op x y) (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq33928 eq17458
    | exact resolve eq17458 eq33928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17458
  have eq33973 : ∀ X0 : G, (σ (k (M.op x y) (M.op x y))) = (k (M.op X0 X0) (σ (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq33928 eq17462
    | exact resolve eq17462 eq33928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17462 eq33928
  have eq34013 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k (M.op X0 X0) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq33973
    | exact resolve eq33973 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33973
  have eq34016 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ (M.op x y))) X0) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq41 eq33969
    | exact resolve eq33969 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33969
  have eq34033 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq41 eq33934
    | exact resolve eq33934 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq33934
  have eq34039 : ∀ X0 : G, (k (σ (M.op x y)) (σ y)) = (k (M.op X0 X0) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26796 eq34013
    | exact resolve eq34013 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34013
  have eq34042 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ y)) X0) = (M.op (k (σ (M.op x y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26796 eq34016
    | exact resolve eq34016 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34016
  have eq34055 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26796 eq34033
    | exact resolve eq34033 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34033
  have eq34061 : ∀ X0 : G, (k (σ (M.op x y)) (σ y)) = (k (M.op X0 X0) (k (σ (M.op x y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq20 eq34039
    | (have j0 := eq34039 X0
       grind)
    | exact resolve eq34039 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34039
  have eq34064 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ y)) X0) = (M.op (k (σ (M.op x y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq34042
    | (have j0 := eq34042 X0
       grind)
    | exact resolve eq34042 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34042
  have eq34069 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq34055
    | exact resolve eq34055 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34055
  have eq34075 : ∀ X0 : G, (k (σ y) (σ y)) = (k (M.op X0 X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq26796 eq34061
    | exact resolve eq34061 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34061
  have eq34078 : ∀ X0 : G, (k (k (σ y) (σ y)) X0) = (M.op (k (σ y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26796 eq34064
    | exact resolve eq34064 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34064
  have eq34083 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26796 eq34069
    | exact resolve eq34069 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34069
  have eq35993 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) := by
    first
    | exact superpose eq34083 eq34075
    | exact resolve eq34075 eq34083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34075 eq34083
  have eq37355 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq555 (k (M.op x x) x) X0 x
       have i₂ := eq2325 X0 x (k (M.op x x) x) x x
       grind)
    | exact superpose eq2325 eq555
    | (have j1 := eq2325 X0 x x x x
       grind)
    | exact resolve eq555 eq2325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq2325
  have eq37515 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq37355 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq37355 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq37355 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37355
  have eq46045 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X0 (M.op X1 X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq561 (k (M.op x x) (k (M.op x (k (M.op x x) x)) X1)) X2
       have i₂ := eq2329 X1 X0 x x x (k (M.op x x) (k (M.op x (k (M.op x x) x)) X1)) x
       grind)
    | exact superpose eq2329 eq561
    | exact resolve eq561 eq2329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq2329
  have eq46239 : ∀ X0 X1 X2 : G, (k X2 X2) = (k (M.op X0 (M.op X1 X1)) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46045 X0 X1 X0
       have i₂ := eq37515 X0
       grind)
    | exact superpose eq37515 eq46045
    | exact resolve eq46045 eq37515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46045
  have eq46619 : ∀ X1 X2 : G, (k X2 X2) = (k (M.op X1 X1) (k X2 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq46239 x X1 X2
       have i₂ := eq181 X1 x
       grind)
    | (have i₁ := eq46239 (M.op X1 X1) X1 X2
       have i₂ := eq181 (M.op X1 X1) X2
       grind)
    | exact superpose eq181 eq46239
    | exact resolve eq46239 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq46239
  have eq46912 : ∀ X1 X2 : G, (k X2 X2) = (k (k X1 X1) (k X2 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq46619 X1 X2
       have i₂ := eq37515 X1
       grind)
    | exact superpose eq37515 eq46619
    | exact resolve eq46619 eq37515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46619
  have eq64828 : ∀ X0 X1 : G, (M.op X0 (k (k (M.op x y) (M.op x y)) X1)) = (k (k (σ y) (σ y)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34078 (M.op X1 X1)
       have i₂ := eq33966 X0 X1 (k sF3 sF3)
       grind)
    | exact superpose eq33966 eq34078
    | exact resolve eq34078 eq33966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33966 eq34078
  have eq65111 : ∀ X0 X1 : G, (M.op X0 (k (k (M.op x y) (M.op x y)) X1)) = (k (k (σ y) (σ y)) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64828 X0 X1
       have i₂ := eq37515 X1
       grind)
    | exact superpose eq37515 eq64828
    | exact resolve eq64828 eq37515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64828
  have eq65349 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (k (k (M.op x y) (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65111 X0 sF3
       have i₂ := eq46912 X1 (k sF3 sF3)
       grind)
    | (have i₁ := eq65111 X0 x
       have i₂ := eq46912 sF3 x
       grind)
    | exact superpose eq46912 eq65111
    | exact resolve eq65111 eq46912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46912 eq65111
  have eq65772 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq65349 eq192
    | exact resolve eq192 eq65349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq289590 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq17456 y x
       have i₂ := eq22656
       grind)
    | exact superpose eq22656 eq17456
    | exact resolve eq17456 eq22656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17456 eq22656
  have eq289787 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq289590 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq289590
    | (have j0 := eq289590 X0
       grind)
    | exact resolve eq289590 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq289590
  have eq289961 : ∀ X0 : G, x = (k y y) ∨ (σ y) = (M.op X0 (σ y)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq289787 X0
       have i₂ := eq37515 y
       grind)
    | exact superpose eq37515 eq289787
    | (have j0 := eq289787 X0
       grind)
    | exact resolve eq289787 eq37515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289787
  have eq289962 : ∀ X0 : G, x = (k y y) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq289961 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289961
  have eq290140 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq289962 X0
       have i₂ := eq26744
       grind)
    | exact superpose eq26744 eq289962
    | (have j0 := eq289962 X0
       grind)
    | exact resolve eq289962 eq26744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26744 eq289962
  have eq290690 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq290140 eq26
    | (have j1 := eq290140 (σ x)
       grind)
    | exact resolve eq26 eq290140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290140
  have eq291069 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq290690 eq26758
    | exact resolve eq26758 eq290690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26758
  have eq291094 : ∀ X0 : G, x = (M.op X0 (k x (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq290690 eq65349
    | exact resolve eq65349 eq290690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65349
  have eq291098 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq290690 eq65772
    | exact resolve eq65772 eq290690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65772 eq290690
  have eq291249 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq291069
    | exact resolve eq291069 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291069
  have eq291317 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26796 eq291249
    | exact resolve eq291249 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291249
  have eq291347 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq291317
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq291317
    | exact resolve eq291317 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291317
  have eq291423 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq291347 eq35993
    | exact resolve eq35993 eq291347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35993 eq291347
  have eq309437 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26755
       have i₂ := eq291098 sF0
       grind)
    | exact superpose eq291098 eq26755
    | exact resolve eq26755 eq291098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291098
  have eq310530 : ∀ X0 : G, x = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq309437 eq291094
    | exact resolve eq291094 eq309437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291094 eq309437
  have eq310541 : ∀ X0 : G, x = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq310530 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310530
  have eq310806 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq310541 eq26755
    | exact resolve eq26755 eq310541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26755 eq310541
  have eq311132 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq310806 eq27
    | exact resolve eq27 eq310806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310806
  have eq311133 : x = (M.op x y) := by
    first
    | (have r₁ := eq311132
       have r₂ := eq26796
       grind)
    | exact resolve eq311132 eq26796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26796 eq311132
  have eq311135 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq311133
       grind)
    | exact superpose eq311133 eq22
    | exact resolve eq22 eq311133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq311133
  have eq311319 : (σ x) = (σ y) := by
    first
    | exact superpose eq311135 eq26756
    | exact resolve eq26756 eq311135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26756
  have eq311320 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq311135 eq20
    | exact resolve eq20 eq311135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq311135
  have eq311815 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq311319 eq26
    | exact resolve eq26 eq311319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq311862 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq311319 eq1113
    | exact resolve eq1113 eq311319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq311985 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq311862
  have eq312041 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq311985
       have i₂ := eq37515 sF2
       grind)
    | exact superpose eq37515 eq311985
    | exact resolve eq311985 eq37515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311985
  have eq312088 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq311815
       have i₂ := eq37515 sF2
       grind)
    | exact superpose eq37515 eq311815
    | exact resolve eq311815 eq37515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37515 eq311815
  have eq312117 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq291423 eq312041
    | exact resolve eq312041 eq291423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291423 eq312041
  have eq312173 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq312088 eq312117
    | exact resolve eq312117 eq312088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312117
  have eq312215 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq312088 eq312173
    | exact resolve eq312173 eq312088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312088 eq312173
  have eq312239 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq311319 eq312215
    | exact resolve eq312215 eq311319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311319 eq312215
  have eq312240 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq312239
  have eq312447 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq312240 eq27
    | exact resolve eq27 eq312240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq312240
  have eq312448 : False := by grind
  exact eq312448
