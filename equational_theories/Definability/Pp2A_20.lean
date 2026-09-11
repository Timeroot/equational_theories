import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation4069 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq110 : ∀ X0 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) x X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 X0 X2
       have i₂ := eq110 X0 X1
       grind)
    | (have i₁ := eq110 X0 X2
       have i₂ := eq110 X0 (M.op X0 X0)
       grind)
    | exact superpose eq110 eq110
    | exact resolve eq110 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (σ X0) x
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq110
    | exact resolve eq110 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq141 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq127
    | exact resolve eq127 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq147 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125 (σ X0) X1 X2
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq125
    | exact resolve eq125 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq462 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq469 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq462 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq462
    | (have j0 := eq462 X0 X1
       grind)
    | exact resolve eq462 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq674 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 X0 X2
       have i₂ := eq125 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq141 X0 X2
       have i₂ := eq125 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq125 eq141
    | exact resolve eq141 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq141
  have eq1057 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq469 x y
       grind)
    | exact superpose eq469 eq16
    | (have j1 := eq469 x y
       grind)
    | exact resolve eq16 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq76285 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq461 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq461
    | exact resolve eq461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq76515 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76285 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq76285
    | (have j0 := eq76285 X0 X1
       grind)
    | exact resolve eq76285 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76285
  have eq117864 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1057
       have i₂ := eq76515 x y
       grind)
    | exact superpose eq76515 eq1057
    | (have j1 := eq76515 x y
       grind)
    | (have r₁ := eq1057
       have r₂ := eq76515 x y
       grind)
    | (have r₁ := eq1057
       have r₂ := eq76515 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1057
       have r₂ := eq76515 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1057 eq76515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq76515
  have eq117865 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq117864
  have eq551883 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq117865
       grind)
    | exact superpose eq117865 eq16
    | exact resolve eq16 eq117865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117865
  have eq551884 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq551883
       have r₂ := eq23 x
       grind)
    | exact resolve eq551883 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551883
  have eq551886 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq551884
       grind)
    | exact superpose eq551884 eq10
    | exact resolve eq10 eq551884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551884
  have eq551950 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq551886
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq551886
    | exact resolve eq551886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551886
  have eq551952 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq551950
       grind)
    | exact superpose eq551950 eq16
    | exact resolve eq16 eq551950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551950
  have eq551953 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq551952
       have r₂ := eq23 x
       grind)
    | exact resolve eq551952 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq551952
  have eq552162 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq551953
       grind)
    | exact superpose eq551953 eq10
    | exact resolve eq10 eq551953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551953
  have eq552226 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq552162
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq552162
    | exact resolve eq552162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552162
  have eq552227 : x = (M.op y y) := by grind
  clear eq552226
  have eq552262 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq147 y X1 x
       have i₂ := eq552227
       grind)
    | exact superpose eq552227 eq147
    | exact resolve eq147 eq552227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq552301 : ∀ X0 X1 : G, (M.op (σ x) X0) = (σ (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq674 y X1 x
       have i₂ := eq552227
       grind)
    | exact superpose eq552227 eq674
    | exact resolve eq674 eq552227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq552227
  have eq561149 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq552262 (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq552262 X0 (σ y)
       grind)
    | exact superpose eq552262 eq16
    | exact resolve eq16 eq552262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552262
  have eq562121 : False := by grind
  exact eq562121

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_y_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
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
  clear eq24
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
  have eq53 : ∀ X0 X1 X4 X5 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 X1 (M.op (M.op x x) x) X4 X5
       have i₂ := eq14 X0 x x X4
       grind)
    | (have i₁ := eq14 X0 X0 X0 x
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X1 (M.op x x) x X4
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq14 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq57 X1 X0
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq57 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq57 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq111 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq98
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq128
    | exact resolve eq128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq129
    | exact resolve eq129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq191 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq232 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (M.op (M.op x y) y) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq54 x X2
       have i₂ := eq54 x X0
       grind)
    | (have i₁ := eq54 (M.op (M.op x y) y) x
       have i₂ := eq54 X0 (M.op (M.op x y) y)
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq55 x X2
       have i₂ := eq55 x X0
       grind)
    | (have i₁ := eq55 (M.op (M.op (σ x) (σ y)) (σ y)) x
       have i₂ := eq55 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq323 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X1)
       have i₂ := eq56 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq56 X0 X1 x
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq56 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq56 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq323 x X1 X2
       grind)
    | (have r₁ := eq323 x X1 X2
       have r₂ := eq57 x X1
       grind)
    | (have r₁ := eq323 X1 x X2
       have r₂ := eq57 x X1
       grind)
    | exact resolve eq323 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq450 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq532 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq331 X2 X1
       have i₂ := eq57 X1 X0
       grind)
    | (have i₁ := eq331 X2 X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq331
    | exact resolve eq331 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 X2))) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 (M.op X2 X2)
       have i₂ := eq532 X0 (τ X1) X2
       grind)
    | exact superpose eq532 eq34
    | exact resolve eq34 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1051 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op X2 X2))) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq450 X1 (M.op X2 X2)
       have i₂ := eq532 X0 (σ X1) X2
       grind)
    | exact superpose eq532 eq450
    | exact resolve eq450 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq532
  have eq1470 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (σ (k X3 X3)) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (σ X3) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq111 X1 X1
       have i₂ := eq53 X0 (σ X1) x x
       grind)
    | exact superpose eq53 eq111
    | exact resolve eq111 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1475 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X1 X1
       have i₂ := eq57 (σ X1) X1
       grind)
    | (have i₁ := eq111 X1 X1
       have i₂ := eq57 X0 (σ X1)
       grind)
    | exact superpose eq57 eq111
    | exact resolve eq111 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1523 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1475 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1528 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (σ (k X3 X3)) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1470 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq7748 : ∀ X0 X3 : G, (σ (M.op X0 X0)) = (σ (M.op X3 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq680 X3 x x
       have i₂ := eq680 X0 x x
       grind)
    | exact superpose eq680 eq680
    | exact resolve eq680 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8108 : ∀ X0 X3 : G, (τ (M.op X0 X0)) = (τ (M.op X3 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1051 X3 x x
       have i₂ := eq1051 X0 x x
       grind)
    | exact superpose eq1051 eq1051
    | exact resolve eq1051 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12252 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1523 X0 (τ X1)
       grind)
    | exact superpose eq1523 eq34
    | (have j1 := eq1523 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq12253 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq43
       have i₂ := eq1523 X0 x
       grind)
    | exact superpose eq1523 eq43
    | (have j1 := eq1523 X0 x
       grind)
    | exact resolve eq43 eq1523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq12278 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12253 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12253
    | (have j0 := eq12253 X0
       grind)
    | exact resolve eq12253 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12253
  have eq12279 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12252 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12252
    | (have j0 := eq12252 X0 X1
       grind)
    | exact resolve eq12252 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12252
  have eq12300 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12279 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12279
    | (have j0 := eq12279 X0 X1
       grind)
    | exact resolve eq12279 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12279
  have eq16966 : ∀ X0 : G, (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq12278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12278
  have eq17357 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12300
  have eq17418 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17357 X2 (σ (M.op X1 X1))
       have i₂ := eq680 X0 (σ (M.op X1 X1)) X1
       grind)
    | exact superpose eq680 eq17357
    | (have j0 := eq17357 X2 (σ (M.op X1 X1))
       grind)
    | (have r₁ := eq17357 X0 (σ (M.op X0 X0))
       have r₂ := eq680 X0 (σ (M.op X0 X0)) X0
       grind)
    | exact resolve eq17357 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq17420 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17357 X2 (τ (M.op X1 X1))
       have i₂ := eq1051 X0 (τ (M.op X1 X1)) X1
       grind)
    | exact superpose eq1051 eq17357
    | (have j0 := eq17357 X2 (τ (M.op X1 X1))
       grind)
    | (have r₁ := eq17357 X0 (τ (M.op X0 X0))
       have r₂ := eq1051 X0 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq17357 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq17427 : ∀ X1 X2 : G, (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq17420 x X1 X2
       grind)
    | (have r₁ := eq17420 x x X2
       have r₂ := eq8108 x x
       grind)
    | (have r₁ := eq17420 x x X2
       have r₂ := eq8108 x x
       grind)
    | exact resolve eq17420 eq8108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8108 eq17420
  have eq17428 : ∀ X1 X2 : G, (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq17418 x X1 X2
       grind)
    | (have r₁ := eq17418 x x X2
       have r₂ := eq7748 x x
       grind)
    | (have r₁ := eq17418 x x X2
       have r₂ := eq7748 x x
       grind)
    | exact resolve eq17418 eq7748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17418
  have eq17892 : ∀ X0 X2 : G, (σ (M.op X2 X2)) = (τ (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq17428 X2 x
       have i₂ := eq17427 X0 x
       grind)
    | exact superpose eq17427 eq17428
    | exact resolve eq17428 eq17427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53277 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq191 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq191
    | (have j0 := eq191 x
       grind)
    | exact resolve eq191 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq53311 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq53277
  have eq53315 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq53311
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq53311
    | exact resolve eq53311 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq53311
  have eq53332 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq81 x (σ x) (σ x)
       grind)
    | (have r₁ := eq53315
       have r₂ := eq81 (σ x) (k (σ x) (σ x)) x
       grind)
    | (have r₁ := eq53315
       have r₂ := eq81 (σ x) (σ x) x
       grind)
    | exact resolve eq53315 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq53315
  have eq53339 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq53332 eq16966
    | (have j0 := eq16966 X0
       grind)
    | exact resolve eq16966 eq53332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16966
  have eq53341 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq53332 eq49
    | exact resolve eq49 eq53332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq53332
  have eq53352 : ∀ X0 : G, (M.op X0 X0) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq53341
       have i₂ := eq17427 sF2 x
       grind)
    | exact superpose eq17427 eq53341
    | exact resolve eq53341 eq17427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17427
  have eq53353 : ∀ X0 : G, (k x x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53341
       have i₂ := eq17892 sF2 x
       grind)
    | exact superpose eq17892 eq53341
    | exact resolve eq53341 eq17892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17892
  have eq53409 : ∀ X0 : G, (k x x) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have i₁ := eq53352 x
       have i₂ := eq54 x X0
       grind)
    | (have i₁ := eq53352 (M.op (M.op x y) y)
       have i₂ := eq54 X0 (M.op (M.op x y) y)
       grind)
    | exact superpose eq54 eq53352
    | exact resolve eq53352 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq53411 : ∀ X0 X1 : G, (k x x) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53352 x
       have i₂ := eq56 X0 x X1
       grind)
    | (have i₁ := eq53352 (M.op X0 X0)
       have i₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq53352
    | exact resolve eq53352 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq53352
  have eq63659 : ∀ X0 X1 X2 X3 : G, (σ (k X3 X3)) = (M.op (k x x) X2) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1528 X0 X1 X2 X3
       have i₂ := eq53411 X0 X1
       grind)
    | exact superpose eq53411 eq1528
    | (have j0 := eq1528 X0 X1 X2 X3
       grind)
    | exact resolve eq1528 eq53411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq63660 : ∀ X2 X3 : G, (σ (k X3 X3)) = (M.op (k x x) X2) ∨ (σ X3) = (M.op (k x x) X2) := by
    intro X2 X3
    first
    | (have i₁ := eq63659 x x X2 X3
       have i₂ := eq53411 x x
       grind)
    | exact superpose eq53411 eq63659
    | (have j0 := eq63659 x x X2 X3
       grind)
    | exact resolve eq63659 eq53411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53411 eq63659
  have eq63663 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (k x x) X1) ∨ (σ (M.op X0 X0)) = (M.op (k x x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63660 X1 (M.op X0 X0)
       have i₂ := eq331 X0 (M.op X0 X0)
       grind)
    | exact superpose eq331 eq63660
    | (have j0 := eq63660 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq63660 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq64176 : ∀ X0 X1 : G, (k x x) = (M.op (k x x) X1) ∨ (σ (M.op X0 X0)) = (M.op (k x x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63663 X0 X1
       have i₂ := eq53353 (M.op X0 X0)
       grind)
    | exact superpose eq53353 eq63663
    | (have j0 := eq63663 X0 X1
       grind)
    | exact resolve eq63663 eq53353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63663
  have eq64333 : ∀ X1 : G, (k x x) = (M.op (k x x) X1) ∨ (k x x) = (M.op (k x x) X1) := by
    intro X1
    first
    | (have i₁ := eq64176 x X1
       have i₂ := eq53353 x
       grind)
    | exact superpose eq53353 eq64176
    | (have j0 := eq64176 x X1
       grind)
    | exact resolve eq64176 eq53353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64176
  have eq64334 : ∀ X1 : G, (k x x) = (M.op (k x x) X1) := by
    intro X1
    first
    | (have j0 := eq64333 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64333
  have eq123126 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq53339 X0
       have i₂ := eq57 sF2 X1
       grind)
    | (have i₁ := eq53339 X0
       have i₂ := eq57 X0 sF2
       grind)
    | exact superpose eq57 eq53339
    | (have j0 := eq53339 X1
       grind)
    | exact resolve eq53339 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq53339
  have eq132354 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq130 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq132362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq132354
    | exact resolve eq132354 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132354
  have eq132367 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq132362
       have r₂ := eq27
       grind)
    | exact resolve eq132362 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132362
  have eq132369 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq132367
    | exact resolve eq132367 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132367
  have eq132374 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq132369 eq53341
    | exact resolve eq53341 eq132369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132369
  have eq132596 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq132374
    | exact resolve eq132374 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132374
  have eq132627 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq17357 x x
       grind)
    | (have r₁ := eq132596
       have r₂ := eq17357 x x
       grind)
    | exact resolve eq132596 eq17357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17357 eq132596
  have eq132721 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7748 X0 x
       have i₂ := eq132627
       grind)
    | exact superpose eq132627 eq7748
    | exact resolve eq7748 eq132627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7748
  have eq132729 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17428 x X0
       have i₂ := eq132627
       grind)
    | exact superpose eq132627 eq17428
    | exact resolve eq17428 eq132627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17428 eq132627
  have eq132842 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq132729 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq132729
    | (have j0 := eq132729 X0
       grind)
    | exact resolve eq132729 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132729
  have eq132849 : (σ x) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq132721 x
       have i₂ := eq53353 x
       grind)
    | exact superpose eq53353 eq132721
    | exact resolve eq132721 eq53353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53353 eq132721
  have eq132897 : (σ x) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq132849
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq132849
    | exact resolve eq132849 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132849
  have eq137279 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq64334 x
       have i₂ := eq132897
       grind)
    | exact superpose eq132897 eq64334
    | exact resolve eq64334 eq132897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132897
  have eq140036 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq137279 eq26
    | (have j1 := eq137279 (σ y)
       grind)
    | exact resolve eq26 eq137279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137279
  have eq140187 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq140036
  have eq140307 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq140187 eq255
    | exact resolve eq255 eq140187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq140357 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq140307
    | (have j0 := eq140307 X1 X0
       grind)
    | exact resolve eq140307 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140307
  have eq140697 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq140187 eq140357
    | exact resolve eq140357 eq140187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140187 eq140357
  have eq141068 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq140697 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140697
  have eq143249 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq141068
    | (have j0 := eq141068 (σ y) X0
       grind)
    | exact resolve eq141068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141068
  have eq143911 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq143249 eq123126
    | (have j0 := eq123126 X0 X0
       grind)
    | exact resolve eq123126 eq143249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123126 eq143249
  have eq144008 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq143911 X0
       have j1 := eq132842 X0
       grind)
    | (have r₁ := eq143911 X0
       have r₂ := eq132842 X0
       grind)
    | exact resolve eq143911 eq132842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132842 eq143911
  have eq146490 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53341
       have i₂ := eq144008 sF2
       grind)
    | exact superpose eq144008 eq53341
    | exact resolve eq53341 eq144008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53341 eq144008
  have eq146537 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq146490
    | exact resolve eq146490 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq146490
  have eq148475 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq64334 x
       have i₂ := eq146537
       grind)
    | exact superpose eq146537 eq64334
    | exact resolve eq64334 eq146537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64334 eq146537
  have eq150445 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq148475 y
       grind)
    | exact superpose eq148475 eq18
    | (have j1 := eq148475 y
       grind)
    | exact resolve eq18 eq148475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148475
  have eq150595 : x = (M.op x y) := by grind
  clear eq150445
  have eq150709 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq150595 eq20
    | exact resolve eq20 eq150595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq150756 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq150595 eq232
    | exact resolve eq232 eq150595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq150793 : ∀ X0 : G, (k x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq150595 eq53409
    | exact resolve eq53409 eq150595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53409
  have eq150797 : ∀ X0 : G, (k x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq150793 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq150793
    | (have j0 := eq150793 X0
       grind)
    | exact resolve eq150793 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150793
  have eq150832 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq150756 X1 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq150756
    | (have j0 := eq150756 X1 X0
       grind)
    | exact resolve eq150756 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150756
  have eq150878 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq150709
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq150709
    | exact resolve eq150709 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150709
  have eq150880 : ∀ X0 : G, (k x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq150595 eq150797
    | exact resolve eq150797 eq150595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150797
  have eq150903 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
    intro X0 X1
    first
    | exact superpose eq150595 eq150832
    | exact resolve eq150832 eq150595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150832
  have eq150990 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq150878 eq26
    | exact resolve eq26 eq150878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq151726 : ∀ X0 : G, (M.op x y) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq150903 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq150903 X0 y
       grind)
    | exact superpose eq150903 eq18
    | (have j1 := eq150903 y X0
       grind)
    | exact resolve eq18 eq150903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq150903
  have eq151947 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq150595 eq151726
    | exact resolve eq151726 eq150595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150595 eq151726
  have eq152095 : x = (k x x) := by
    first
    | (have i₁ := eq151947 x
       have i₂ := eq150880 x
       grind)
    | exact superpose eq150880 eq151947
    | exact resolve eq151947 eq150880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150880
  have eq152633 : ∀ X0 : G, (σ x) = (M.op x X0) ∨ (σ x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq63660 x x
       have i₂ := eq152095
       grind)
    | exact superpose eq152095 eq63660
    | exact resolve eq63660 eq152095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63660 eq152095
  have eq152643 : ∀ X0 : G, (σ x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq152633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152633
  have eq152653 : x = (σ x) := by
    first
    | (have i₁ := eq152643 x
       have i₂ := eq151947 x
       grind)
    | exact superpose eq151947 eq152643
    | exact resolve eq152643 eq151947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152643
  have eq152671 : x = (σ x) := by
    first
    | (have i₁ := eq152653
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq152653
    | exact resolve eq152653 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq152653
  have eq152688 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq150878 eq152671
    | exact resolve eq152671 eq150878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150878 eq152671
  have eq152746 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq152688 eq150990
    | exact resolve eq150990 eq152688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150990
  have eq152748 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq152746
       have i₂ := eq151947 sF3
       grind)
    | exact superpose eq151947 eq152746
    | exact resolve eq152746 eq151947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151947 eq152746
  have eq152805 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq152748 eq27
    | exact resolve eq27 eq152748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq152748
  have eq152872 : False := by grind
  exact eq152872

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation4111 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq16 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq182 X1 X0
       grind)
    | (have i₁ := eq174 X1
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq174
    | exact resolve eq174 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq221 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq205 X1 X0
       grind)
    | exact superpose eq205 eq174
    | exact resolve eq174 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (M.op (M.op x y) y) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq179 x X2
       have i₂ := eq179 x X0
       grind)
    | (have i₁ := eq179 (M.op (M.op x y) y) x
       have i₂ := eq179 X0 (M.op (M.op x y) y)
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq560 : ∀ X0 X2 : G, (k X2 X2) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq205 x X2
       have i₂ := eq180 x X0
       grind)
    | (have i₁ := eq205 (M.op (M.op (σ x) (σ y)) (σ y)) x
       have i₂ := eq180 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq180 eq205
    | exact resolve eq205 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1573 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq1574 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1617 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1615
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1615
    | exact resolve eq1615 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615
  have eq4413 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq39
    | exact resolve eq39 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq4414 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4413
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4413
    | exact resolve eq4413 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4413
  have eq4416 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq4414
    | exact resolve eq4414 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4414
  have eq5397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4416 eq1574
    | exact resolve eq1574 eq4416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq5406 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq5397
       have r₂ := eq27
       grind)
    | exact resolve eq5397 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5397
  have eq5420 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq5406 eq1617
    | (have r₁ := eq1617
       have r₂ := eq5406
       grind)
    | exact resolve eq1617 eq5406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq5422 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq5420
  have eq5423 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq5422
  have eq5425 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4416 eq5423
    | exact resolve eq5423 eq4416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4416 eq5423
  have eq5456 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5425 eq221
    | exact resolve eq221 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq5425
  have eq5549 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq560 X1 x
       have i₂ := eq5456 x
       grind)
    | exact superpose eq5456 eq560
    | exact resolve eq560 eq5456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq5456
  have eq5635 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq5406 eq5549
    | exact resolve eq5549 eq5406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5549
  have eq5679 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq26 eq5635
    | (have j0 := eq5635 X1
       grind)
    | exact resolve eq5635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq5697 : ∀ X1 : G, (σ (M.op x y)) = (M.op (σ x) X1) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq5406 eq5679
    | exact resolve eq5679 eq5406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5406 eq5679
  have eq6606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq5697 eq26
    | (have j1 := eq5697 (σ y)
       grind)
    | exact resolve eq26 eq5697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5697
  have eq6620 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq6606
       have r₂ := eq27
       grind)
    | exact resolve eq6606 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6606
  have eq6629 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6620 eq31
    | exact resolve eq31 eq6620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq6620
  have eq6665 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq6629
    | exact resolve eq6629 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6629
  have eq6666 : x = (M.op x y) ∨ x = y := by grind
  clear eq6665
  have eq6672 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq6666
       grind)
    | exact superpose eq6666 eq18
    | exact resolve eq18 eq6666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6673 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq6666
       grind)
    | exact superpose eq6666 eq22
    | exact resolve eq22 eq6666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6666
  have eq6674 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq6673
    | exact resolve eq6673 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6673
  have eq6713 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq6672 eq505
    | exact resolve eq505 eq6672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq6808 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq6713 eq6672
    | exact resolve eq6672 eq6713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6672 eq6713
  have eq6817 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq6808 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6808
  have eq6887 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6817 eq205
    | exact resolve eq205 eq6817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq7288 : ∀ X0 : G, (M.op x y) = (σ (k X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq6887 (σ X0)
       grind)
    | exact superpose eq6887 eq10
    | exact resolve eq10 eq6887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7294 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq37 sF0
       have i₂ := eq6887 sF0
       grind)
    | exact superpose eq6887 eq37
    | exact resolve eq37 eq6887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq7320 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq7294
    | exact resolve eq7294 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7294
  have eq7326 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq6887 eq7288
    | exact resolve eq7288 eq6887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7288
  have eq7395 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq6674 eq7320
    | exact resolve eq7320 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674 eq7320
  have eq7400 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq7326
    | exact resolve eq7326 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7326
  have eq7447 : (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq6887 eq7395
    | exact resolve eq7395 eq6887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6887 eq7395
  have eq7570 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq7447 eq26
    | exact resolve eq26 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7447
  have eq7603 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6817 eq7570
    | exact resolve eq7570 eq6817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6817 eq7570
  have eq7618 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq7603 eq27
    | exact resolve eq27 eq7603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7603
  have eq7643 : x = y := by
    first
    | (have r₁ := eq7618
       have r₂ := eq7400
       grind)
    | exact resolve eq7618 eq7400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7400 eq7618
  have eq7968 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7643
       grind)
    | exact superpose eq7643 eq18
    | exact resolve eq18 eq7643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7969 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq7643
       grind)
    | exact superpose eq7643 eq24
    | exact resolve eq24 eq7643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7643
  have eq7984 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq7969
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7969
    | exact resolve eq7969 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7969
  have eq7985 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq7968
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq7968
    | exact resolve eq7968 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7968
  have eq7986 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7984 eq26
    | exact resolve eq26 eq7984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7984
  have eq8019 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq7986
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq7986
    | exact resolve eq7986 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq7986
  have eq8026 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq7985
       grind)
    | exact superpose eq7985 eq39
    | exact resolve eq39 eq7985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq7985
  have eq8071 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8026
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8026
    | exact resolve eq8026 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8026
  have eq8081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8019 eq8071
    | exact resolve eq8071 eq8019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8019 eq8071
  have eq8087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8081
    | exact resolve eq8081 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8081
  have eq8089 : False := by grind
  exact eq8089

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_x_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq427 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq436 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq436 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq436 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq436 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq447 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq427 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq427 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq427 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq655 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq447 X0 X1
       grind)
    | exact superpose eq447 eq9
    | (have j1 := eq447 X0 X1
       grind)
    | exact resolve eq9 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq664 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq655 X0 X1
       have j1 := eq438 X1 X0
       grind)
    | (have r₁ := eq655 X1 X1
       have r₂ := eq438 X0 X1
       grind)
    | exact resolve eq655 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq655
  have eq690 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq664 (σ X1) (σ X0)
       grind)
    | exact superpose eq664 eq15
    | exact resolve eq15 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1
       have i₂ := eq664 X1 X0
       grind)
    | exact superpose eq664 eq690
    | exact resolve eq690 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq690
  have eq965 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq717 x y
       grind)
    | exact superpose eq717 eq16
    | (have r₁ := eq16
       have r₂ := eq717 x y
       grind)
    | exact resolve eq16 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq983 : False := by grind
  exact eq983

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pyy_pyx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq62
  have eq79 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq109 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq133 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq97 (τ X0) X1
       grind)
    | exact superpose eq97 eq17
    | (have j1 := eq97 (τ X0) X1
       grind)
    | exact resolve eq17 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq97
  have eq520 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq133
    | exact resolve eq133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq564 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq520
    | (have j0 := eq520 X0 X1
       grind)
    | exact resolve eq520 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq581 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq564 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq564
    | (have j0 := eq564 (τ X0) (τ X1)
       grind)
    | exact resolve eq564 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq581
    | (have j0 := eq581 X0 X1
       grind)
    | exact resolve eq581 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq946 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131 x y
       grind)
    | exact superpose eq131 eq16
    | (have j1 := eq131 x y
       grind)
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq966 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq1429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq946
       have i₂ := eq564 x y
       grind)
    | exact superpose eq564 eq946
    | (have j1 := eq564 (σ x) (σ y)
       grind)
    | (have r₁ := eq946
       have r₂ := eq564 x y
       grind)
    | exact resolve eq946 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1430 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1429
  have eq1460 : y ≠ y ∨ (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1430
       grind)
    | exact superpose eq1430 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1430
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1430
       grind)
    | exact resolve eq12 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1473 : (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1460
  have eq1476 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq946
       have i₂ := eq1473
       grind)
    | exact superpose eq1473 eq946
    | exact resolve eq946 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq1481 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq966 x y
       have i₂ := eq1473
       grind)
    | exact superpose eq1473 eq966
    | (have j0 := eq966 x y
       grind)
    | exact resolve eq966 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq1473
  have eq1484 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1481
  have eq1485 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1476
  have eq2334 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq624 X1 X0
       grind)
    | exact superpose eq624 eq12
    | (have j0 := eq12 (τ X1) (τ X0)
       have j1 := eq624 X1 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq624 X0 X1
       grind)
    | exact resolve eq12 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq2352 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq2334 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2367 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2352 X0 X1
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq2352
    | (have j0 := eq2352 X0 X1
       grind)
    | exact resolve eq2352 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq2352
  have eq2384 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ (k X1 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2367 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq2367
    | (have j0 := eq2367 X0 X1
       grind)
    | exact resolve eq2367 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2367
  have eq4399 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2384 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2384
    | (have j0 := eq2384 (σ X0) X1
       grind)
    | exact resolve eq2384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384
  have eq4459 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4399 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq4399
    | (have j0 := eq4399 X0 X1
       grind)
    | exact resolve eq4399 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4399
  have eq4466 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4459 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq4459
    | (have j0 := eq4459 X0 X1
       grind)
    | exact resolve eq4459 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459
  have eq4467 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4466 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4466
    | (have j0 := eq4466 X0 X1
       grind)
    | exact resolve eq4466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq4631 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4467 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4467
    | exact resolve eq4467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467
  have eq4706 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4631 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4631
    | (have j0 := eq4631 X0 X1
       grind)
    | exact resolve eq4631 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4631
  have eq4760 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq4706 X0 X1
       grind)
    | exact superpose eq4706 eq10
    | (have j1 := eq4706 X0 X1
       grind)
    | exact resolve eq10 eq4706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4706
  have eq4809 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4760 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4760
    | (have j0 := eq4760 X0 X1
       grind)
    | exact resolve eq4760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4760
  have eq5014 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4809 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4809
    | exact resolve eq4809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4809
  have eq5144 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5014 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq5014
    | (have j0 := eq5014 X0 X1
       grind)
    | exact resolve eq5014 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5014
  have eq7856 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5144 x y
       grind)
    | exact superpose eq5144 eq16
    | (have j1 := eq5144 x y
       grind)
    | exact resolve eq16 eq5144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144
  have eq7968 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7856
       have i₂ := eq564 x y
       grind)
    | exact superpose eq564 eq7856
    | (have j1 := eq564 x y
       grind)
    | (have r₁ := eq7856
       have r₂ := eq564 x y
       grind)
    | exact resolve eq7856 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq7856
  have eq7969 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq7968
  have eq8139 : y = (M.op y (M.op y (M.op y y))) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq7969
       grind)
    | exact superpose eq7969 eq9
    | exact resolve eq9 eq7969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8345 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq8139
       grind)
    | exact superpose eq8139 eq9
    | exact resolve eq9 eq8139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8139
  have eq8390 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1484
       have i₂ := eq8345
       grind)
    | exact superpose eq8345 eq1484
    | exact resolve eq1484 eq8345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484 eq8345
  have eq8417 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq8390
  have eq8424 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8417
       have r₂ := eq1485
       grind)
    | exact resolve eq8417 eq1485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485 eq8417
  have eq8591 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8424
       grind)
    | exact superpose eq8424 eq16
    | exact resolve eq16 eq8424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8597 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq8424
       grind)
    | exact superpose eq8424 eq9
    | exact resolve eq9 eq8424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8424
  have eq8627 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq8597
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq8597
    | exact resolve eq8597 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8597
  have eq8650 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq8591
       have i₂ := eq7969
       grind)
    | exact superpose eq7969 eq8591
    | exact resolve eq8591 eq7969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7969
  have eq8653 : (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq8650
  have eq9095 : (M.op y y) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq8653
       grind)
    | exact superpose eq8653 eq10
    | exact resolve eq10 eq8653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8653
  have eq9157 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq9095
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq9095
    | exact resolve eq9095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9095
  have eq9621 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq8627
       grind)
    | exact superpose eq8627 eq79
    | exact resolve eq79 eq8627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq8627
  have eq9662 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9621
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq9621
    | exact resolve eq9621 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq9621
  have eq9677 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq9662
       have i₂ := eq9157
       grind)
    | exact superpose eq9157 eq9662
    | exact resolve eq9662 eq9157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9157 eq9662
  have eq9690 : False := by grind
  exact eq9690

/-- `Equation4167`: `x ◇ y = ((y ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation4167 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4167 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4167.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq58 (τ X0)
       grind)
    | exact superpose eq58 eq18
    | exact resolve eq18 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq73 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq67
    | exact resolve eq67 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq73
    | exact resolve eq73 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq73
  have eq88 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq101
    | (have j0 := eq101 X0 X1
       grind)
    | exact resolve eq101 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq101
  have eq439 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq103
    | (have j0 := eq103 X0 X1
       grind)
    | exact resolve eq103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq471 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq439
    | (have j0 := eq439 X0 X1
       grind)
    | exact resolve eq439 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq439
  have eq476 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq471 X0 X1
       have j1 := eq88 X1 X0
       grind)
    | (have r₁ := eq471 X0 X0
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq471 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq471
  have eq481 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq476
    | (have j0 := eq476 X0 X1
       grind)
    | exact resolve eq476 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq476
  have eq722 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq481 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq481
    | exact resolve eq481 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq790 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq722 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq722 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq722 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq722 X0 X1
       grind)
    | exact resolve eq13 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq790 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq806 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq798 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq798 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq798 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq922 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq806 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq927 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq922 X0 X1
       have j1 := eq722 X1 X0
       grind)
    | (have r₁ := eq922 X0 X0
       have r₂ := eq722 X0 X0
       grind)
    | (have r₁ := eq922 X1 X0
       have r₂ := eq722 X0 X1
       grind)
    | exact resolve eq922 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq922
  have eq1065 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq927 (σ X0) (σ X1)
       grind)
    | exact superpose eq927 eq15
    | exact resolve eq15 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X0 X1
       have i₂ := eq927 X0 X1
       grind)
    | exact superpose eq927 eq1065
    | exact resolve eq1065 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq1065
  have eq1739 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1088 x y
       grind)
    | exact superpose eq1088 eq16
    | (have r₁ := eq16
       have r₂ := eq1088 x y
       grind)
    | exact resolve eq16 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1757 : False := by grind
  exact eq1757

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_x_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq64 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq64 X0
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq93 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq93 (σ X0) (σ X1)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq96
    | exact resolve eq96 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq96
  have eq249 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107 x y
       grind)
    | exact superpose eq107 eq16
    | (have r₁ := eq16
       have r₂ := eq107 x y
       grind)
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq257 : False := by grind
  exact eq257

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_x_pyy_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq74 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x (M.op X0 x)))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq76 (M.op X0 X1)
       grind)
    | exact superpose eq76 eq9
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq113 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
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
  have eq419 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq113
    | exact resolve eq113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq450 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq419
    | (have j0 := eq419 X0 X1
       grind)
    | exact resolve eq419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq458 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq450 X1 X0
       grind)
    | exact superpose eq450 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq450 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq450 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq450 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq450 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 (M.op X1 X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 X0
       have i₂ := eq450 X1 X0
       grind)
    | exact superpose eq450 eq79
    | (have j1 := eq450 X1 X0
       grind)
    | exact resolve eq79 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq458 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq484 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq483 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq495 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq484
    | (have j0 := eq484 X0 X1
       grind)
    | exact resolve eq484 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq509 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq495 X0 X1
       grind)
    | exact superpose eq495 eq10
    | (have j1 := eq495 X0 X1
       grind)
    | exact resolve eq10 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq509 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq509
    | (have j0 := eq509 X0 X1
       grind)
    | exact resolve eq509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq563 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq542 X0 (σ X1)
       grind)
    | exact superpose eq542 eq34
    | (have j1 := eq542 (k (σ X1) X0) X0
       grind)
    | exact resolve eq34 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq542
  have eq665 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 (M.op X1 X0)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq460 X0 X1
       grind)
    | exact superpose eq460 eq10
    | (have j1 := eq460 X0 X1
       grind)
    | exact resolve eq10 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq700 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq665
    | (have j0 := eq665 X0 X1
       grind)
    | exact resolve eq665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq715 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111 x y
       grind)
    | exact superpose eq111 eq16
    | (have j1 := eq111 x y
       grind)
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq3144 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) X0
       have i₂ := eq563 (σ X0) X1
       grind)
    | exact superpose eq563 eq26
    | (have j1 := eq563 (σ X1) X0
       grind)
    | exact resolve eq26 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq563
  have eq3188 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3144 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3144
    | (have j0 := eq3144 X0 X1
       grind)
    | exact resolve eq3144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3144
  have eq3218 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3188 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3188
    | (have j0 := eq3188 X0 X1
       grind)
    | exact resolve eq3188 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3188
  have eq3225 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3218 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3218
    | (have j0 := eq3218 X0 X1
       grind)
    | exact resolve eq3218 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3218
  have eq3492 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq3225 X1 X0
       grind)
    | exact superpose eq3225 eq11
    | (have j1 := eq3225 X1 X0
       grind)
    | exact resolve eq11 eq3225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225
  have eq4479 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3492 y x
       grind)
    | exact superpose eq3492 eq16
    | (have j1 := eq3492 y x
       grind)
    | exact resolve eq16 eq3492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3492
  have eq4525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq4479
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq4479
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq4479
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4479
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4479 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4527 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq4479
       have i₂ := eq495 x y
       grind)
    | exact superpose eq495 eq4479
    | (have j1 := eq495 x y
       grind)
    | (have r₁ := eq4479
       have r₂ := eq495 x y
       grind)
    | (have r₁ := eq4479
       have r₂ := eq495 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4479
       have r₂ := eq495 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4479 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq4479
  have eq4528 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4527
  have eq4529 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq4528
  have eq4531 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq4525
  have eq4533 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4529
       grind)
    | exact superpose eq4529 eq16
    | exact resolve eq16 eq4529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4529
  have eq4534 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq4533
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq4533
    | exact resolve eq4533 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4533
  have eq4535 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq4534
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq4534
    | exact resolve eq4534 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4534
  have eq4536 : x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq4535
  have eq4542 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4531
       grind)
    | exact superpose eq4531 eq16
    | exact resolve eq16 eq4531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4531
  have eq4543 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4542
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq4542
    | exact resolve eq4542 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4542
  have eq4544 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4543
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq4543
    | exact resolve eq4543 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4543
  have eq4545 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq4544
  have eq4549 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq79 y x
       have i₂ := eq4545
       grind)
    | exact superpose eq4545 eq79
    | exact resolve eq79 eq4545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq4545
  have eq4572 : y = (M.op y (M.op y x)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq74 y x
       have i₂ := eq4549
       grind)
    | exact superpose eq4549 eq74
    | exact resolve eq74 eq4549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq4549
  have eq4590 : (σ x) = (σ y) ∨ y = (M.op y (M.op y x)) := by grind
  clear eq4572
  have eq4596 : y = (τ (σ x)) ∨ y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4590
       grind)
    | exact superpose eq4590 eq10
    | exact resolve eq10 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4590
  have eq4638 : x = y ∨ y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq4596
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4596
    | exact resolve eq4596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4596
  have eq4640 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4638
       grind)
    | exact superpose eq4638 eq16
    | exact resolve eq16 eq4638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4638
  have eq4641 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq4640
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq4640
    | exact resolve eq4640 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4640
  have eq4642 : (σ x) ≠ (σ x) ∨ y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq4641
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq4641
    | exact resolve eq4641 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4641
  have eq4643 : y = (M.op y (M.op y x)) := by grind
  clear eq4642
  have eq4648 : x = y ∨ (σ (M.op x y)) = (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4643
       have i₂ := eq450 y x
       grind)
    | exact superpose eq450 eq4643
    | (have j1 := eq450 y x
       grind)
    | exact resolve eq4643 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643
  have eq4990 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4648
       grind)
    | exact superpose eq4648 eq16
    | exact resolve eq16 eq4648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4648
  have eq5002 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4990
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq4990
    | exact resolve eq4990 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4990
  have eq5005 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5002
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq5002
    | exact resolve eq5002 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5002
  have eq5006 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq5005
  have eq5026 : x = y ∨ (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq450 y x
       have i₂ := eq5006
       grind)
    | exact superpose eq5006 eq450
    | (have j0 := eq450 y x
       grind)
    | exact resolve eq450 eq5006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq5006
  have eq5039 : x = y ∨ (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq5026
  have eq5045 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5039
       grind)
    | exact superpose eq5039 eq16
    | exact resolve eq16 eq5039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039
  have eq5058 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq5045
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq5045
    | exact resolve eq5045 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5045
  have eq5061 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq5058
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq5058
    | exact resolve eq5058 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5058
  have eq5062 : (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq5061
  have eq5068 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5062
       have i₂ := eq4536
       grind)
    | exact superpose eq4536 eq5062
    | exact resolve eq5062 eq4536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4536
  have eq5156 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq715
       have i₂ := eq5062
       grind)
    | exact superpose eq5062 eq715
    | (have r₁ := eq715
       have r₂ := eq5062
       grind)
    | exact resolve eq715 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq5161 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq5156
  have eq5167 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5068
       grind)
    | exact superpose eq5068 eq10
    | exact resolve eq10 eq5068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068
  have eq5209 : x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5167
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5167
    | exact resolve eq5167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5167
  have eq5211 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5209
       grind)
    | exact superpose eq5209 eq16
    | exact resolve eq16 eq5209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5209
  have eq5228 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5211
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq5211
    | exact resolve eq5211 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5211
  have eq5231 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5228
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq5228
    | exact resolve eq5228 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5228
  have eq5232 : (σ (M.op x y)) = (σ x) := by grind
  clear eq5231
  have eq6452 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq700 (σ x) (σ y)
       have i₂ := eq5161
       grind)
    | exact superpose eq5161 eq700
    | (have j0 := eq700 (σ x) (σ y)
       grind)
    | exact resolve eq700 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq6459 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq6452
  have eq6472 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6459
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6459
    | exact resolve eq6459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6459
  have eq6481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6472
       have i₂ := eq5062
       grind)
    | exact superpose eq5062 eq6472
    | exact resolve eq6472 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5062 eq6472
  have eq6487 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6481
       have r₂ := eq16
       grind)
    | exact resolve eq6481 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6481
  have eq6495 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5161
       have i₂ := eq6487
       grind)
    | exact superpose eq6487 eq5161
    | exact resolve eq5161 eq6487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5161 eq6487
  have eq6528 : (σ x) = (σ y) := by grind
  clear eq6495
  have eq6542 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6528
       grind)
    | exact superpose eq6528 eq16
    | exact resolve eq16 eq6528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6528
  have eq6586 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq6542
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq6542
    | exact resolve eq6542 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq6542
  have eq6587 : False := by grind
  exact eq6587
