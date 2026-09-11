import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq205 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq231 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq205
    | (have j0 := eq205 X0 X1
       grind)
    | exact resolve eq205 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq205
  have eq236 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq231 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq231 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq231 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq231 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq239 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq236
    | (have j0 := eq236 X0 X1
       grind)
    | exact resolve eq236 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq236
  have eq437 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq239
    | exact resolve eq239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq239 (σ X0) X1
       grind)
    | exact superpose eq239 eq15
    | (have j1 := eq239 (σ X0) X1
       grind)
    | exact resolve eq15 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq468 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq448
    | (have j0 := eq448 X0 X1
       grind)
    | exact resolve eq448 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq493 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq437 X1 (σ X0)
       grind)
    | exact superpose eq437 eq24
    | (have j1 := eq437 X1 (σ X0)
       grind)
    | exact resolve eq24 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq503 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq437 (τ X1) X0
       grind)
    | exact superpose eq437 eq17
    | (have j1 := eq437 (τ X1) X0
       grind)
    | exact resolve eq17 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq437
  have eq514 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq493
    | (have j0 := eq493 X0 X1
       grind)
    | exact resolve eq493 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq2289 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq503 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq503
    | exact resolve eq503 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq2355 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2289 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2289
    | (have j0 := eq2289 X0 X1
       grind)
    | exact resolve eq2289 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2289
  have eq7707 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq468 x y
       grind)
    | exact superpose eq468 eq16
    | (have j1 := eq468 x y
       grind)
    | exact resolve eq16 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7746 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq468 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq7922 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq7707
       have i₂ := eq2355 y x
       grind)
    | exact superpose eq2355 eq7707
    | (have j1 := eq2355 y x
       grind)
    | (have r₁ := eq7707
       have r₂ := eq2355 y x
       grind)
    | exact resolve eq7707 eq2355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7707
  have eq7923 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7922
  have eq7927 : y ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq7923
       grind)
    | exact superpose eq7923 eq12
    | exact resolve eq12 eq7923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7928 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq7923
       grind)
    | exact superpose eq7923 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq7923
       grind)
    | exact resolve eq13 eq7923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7923
  have eq7935 : (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7928
  have eq7936 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7927
       have r₂ := eq7935
       grind)
    | exact resolve eq7927 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7927 eq7935
  have eq8109 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq223 x y
       have i₂ := eq7936
       grind)
    | exact superpose eq7936 eq223
    | (have j0 := eq223 x y
       grind)
    | exact resolve eq223 eq7936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq8120 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8109
  have eq8121 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq8120
  have eq8134 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq514 x (σ y)
       have i₂ := eq8121
       grind)
    | exact superpose eq8121 eq514
    | (have j0 := eq514 x (σ y)
       grind)
    | exact resolve eq514 eq8121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq8138 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq8121
       grind)
    | exact superpose eq8121 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8121
       grind)
    | exact resolve eq12 eq8121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8145 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq8121
  have eq8146 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq8138
  have eq8147 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq8146
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8146
    | exact resolve eq8146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8146
  have eq8149 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq8134
       have r₂ := eq8145
       grind)
    | exact resolve eq8134 eq8145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8134
  have eq8154 : y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq8149
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8149
    | exact resolve eq8149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8149
  have eq8231 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7936
       have i₂ := eq8154
       grind)
    | exact superpose eq8154 eq7936
    | exact resolve eq7936 eq8154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8154
  have eq8254 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq8231
  have eq8265 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq8254
       grind)
    | exact superpose eq8254 eq12
    | exact resolve eq12 eq8254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8266 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq8254
       grind)
    | exact superpose eq8254 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq8254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8254
  have eq8273 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8266
       have r₂ := eq67 x
       grind)
    | exact resolve eq8266 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8266
  have eq8274 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8265
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8265
    | exact resolve eq8265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8265
  have eq8275 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8273
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8273
    | exact resolve eq8273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8273
  have eq8276 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8275
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq8275
    | exact resolve eq8275 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8275
  have eq8277 : y = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq8276
       have r₂ := eq8274
       grind)
    | exact resolve eq8276 eq8274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8274 eq8276
  have eq8535 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq8145
       have i₂ := eq8277
       grind)
    | exact superpose eq8277 eq8145
    | exact resolve eq8145 eq8277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8145 eq8277
  have eq8536 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq8535
  have eq8636 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq8147
       grind)
    | exact superpose eq8147 eq12
    | exact resolve eq12 eq8147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8637 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq8147
       grind)
    | exact superpose eq8147 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq8147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8147
  have eq8644 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq8637
       have r₂ := eq67 x
       grind)
    | exact resolve eq8637 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8637
  have eq8645 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq8636
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8636
    | exact resolve eq8636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8636
  have eq8646 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq8644
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8644
    | exact resolve eq8644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8644
  have eq8647 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq8646
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq8646
    | exact resolve eq8646 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq8646
  have eq8648 : (σ y) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq8647
       have r₂ := eq8645
       grind)
    | exact resolve eq8647 eq8645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8645 eq8647
  have eq8945 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq8648
  have eq9728 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7746 x y
       have i₂ := eq7936
       grind)
    | exact superpose eq7936 eq7746
    | (have j0 := eq7746 x y
       grind)
    | exact resolve eq7746 eq7936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7746 eq7936
  have eq9756 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq9728
  have eq9757 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq9756
  have eq9945 : (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq8536
       have i₂ := eq9757
       grind)
    | exact superpose eq9757 eq8536
    | exact resolve eq8536 eq9757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8536
  have eq9946 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9757
       grind)
    | exact superpose eq9757 eq16
    | exact resolve eq16 eq9757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9757
  have eq9965 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq9945
       have r₂ := eq8945
       grind)
    | exact resolve eq9945 eq8945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8945 eq9945
  have eq10086 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2355 y x
       have i₂ := eq9965
       grind)
    | exact superpose eq9965 eq2355
    | (have j0 := eq2355 y x
       grind)
    | exact resolve eq2355 eq9965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355 eq9965
  have eq10171 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq10086
       have r₂ := eq9946
       grind)
    | exact resolve eq10086 eq9946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10086
  have eq10307 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9946
       have i₂ := eq10171
       grind)
    | exact superpose eq10171 eq9946
    | exact resolve eq9946 eq10171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9946 eq10171
  have eq10318 : False := by grind
  exact eq10318

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4334 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq73
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq4395 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4334 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq4334
    | (have j0 := eq4334 X0 X0
       grind)
    | exact resolve eq4334 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq5122 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq4395 X0 X2
       grind)
    | exact superpose eq4395 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq4395 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq4395 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq4395 X1 X1
       grind)
    | exact resolve eq12 eq4395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq5153 : ∀ X0 X1 X2 : G, (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq5122 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5122
  have eq8485 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq5153 X0 X2 X1
       grind)
    | exact superpose eq5153 eq11
    | (have j1 := eq5153 X0 X2 X1
       grind)
    | exact resolve eq11 eq5153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5153
  have eq8611 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8485 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq8485
    | (have j0 := eq8485 X0 X1 X1
       grind)
    | exact resolve eq8485 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8485
  have eq8719 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = X0 ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq8611 X0 (τ X1) X2
       grind)
    | exact superpose eq8611 eq17
    | (have j1 := eq8611 X0 X2 X2
       grind)
    | exact resolve eq17 eq8611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq8775 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8611 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8611
  have eq8776 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8775 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8775
  have eq8995 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq8776 (σ X1) (σ X0)
       grind)
    | exact superpose eq8776 eq15
    | (have j1 := eq8776 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq8776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8776
  have eq10412 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8995 x y
       grind)
    | exact superpose eq8995 eq16
    | (have j1 := eq8995 x y
       grind)
    | exact resolve eq16 eq8995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10461 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8995 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8995
  have eq10612 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10461 (τ X1) (τ X0)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq10461
    | (have j0 := eq10461 (τ X1) (τ X0)
       grind)
    | exact resolve eq10461 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq10667 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10612 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq10612
    | (have j0 := eq10612 X0 X1
       grind)
    | exact resolve eq10612 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10612
  have eq10695 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10667 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq10667
    | (have j0 := eq10667 X0 X1
       grind)
    | exact resolve eq10667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10667
  have eq10716 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10695 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10695
    | (have j0 := eq10695 X0 X1
       grind)
    | exact resolve eq10695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10695
  have eq10731 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10716 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10716
    | (have j0 := eq10716 X0 X1
       grind)
    | exact resolve eq10716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10716
  have eq88009 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (τ X1) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq8719 X0 X1 X2
       grind)
    | exact superpose eq8719 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq8719 X0 X1 X2
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq8719 X0 X1 X2
       grind)
    | exact resolve eq13 eq8719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8719
  have eq88073 : ∀ X0 X1 X2 : G, (k (τ X1) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq88009 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88009
  have eq88129 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = (M.op X0 X2) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq88073 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq88073 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq88073 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88073
  have eq90036 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = (M.op X1 X2) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88129 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq88129
    | (have j0 := eq88129 X1 X1 X2
       grind)
    | exact resolve eq88129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88129
  have eq90438 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = (M.op X1 X2) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90036 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq90036
    | (have j0 := eq90036 X0 X1 X2
       grind)
    | exact resolve eq90036 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90036
  have eq90883 : ∀ X0 X1 X2 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq90438 X1 X0 X2
       grind)
    | exact superpose eq90438 eq10
    | (have j1 := eq90438 X1 X0 X2
       grind)
    | exact resolve eq10 eq90438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90438
  have eq91151 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90883 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq90883
    | (have j0 := eq90883 X0 X1 X1
       grind)
    | exact resolve eq90883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90883
  have eq91636 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq91151 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91151
  have eq91638 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq91636 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91636
  have eq92380 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10412
       have i₂ := eq91638 y x
       grind)
    | exact superpose eq91638 eq10412
    | (have j1 := eq91638 y x
       grind)
    | exact resolve eq10412 eq91638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10412
  have eq92382 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq91638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91638
  have eq92384 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq92380
  have eq93098 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq92382 (σ y) (σ x)
       have i₂ := eq92384
       grind)
    | exact superpose eq92384 eq92382
    | (have j0 := eq92382 (σ y) (σ x)
       grind)
    | (have r₁ := eq92382 (σ y) (σ x)
       have r₂ := eq92384
       grind)
    | exact resolve eq92382 eq92384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92384
  have eq93099 : (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by grind
  clear eq93098
  have eq93101 : x = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq93099
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq93099
    | exact resolve eq93099 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93099
  have eq94043 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10461 x y
       have i₂ := eq93101
       grind)
    | exact superpose eq93101 eq10461
    | (have j0 := eq10461 x y
       grind)
    | (have r₁ := eq10461 x y
       have r₂ := eq93101
       grind)
    | exact resolve eq10461 eq93101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93101
  have eq94130 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq94043
  have eq94141 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq10461 x y
       grind)
    | (have r₁ := eq94130
       have r₂ := eq10461 x y
       grind)
    | exact resolve eq94130 eq10461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10461 eq94130
  have eq94152 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94141
       grind)
    | exact superpose eq94141 eq16
    | exact resolve eq16 eq94141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94161 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq92382 (σ y) (σ x)
       have i₂ := eq94141
       grind)
    | exact superpose eq94141 eq92382
    | (have j0 := eq92382 (σ y) (σ x)
       grind)
    | (have r₁ := eq92382 (σ y) (σ x)
       have r₂ := eq94141
       grind)
    | exact resolve eq92382 eq94141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92382 eq94141
  have eq94162 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq94161
  have eq94164 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq94162
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq94162
    | exact resolve eq94162 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94162
  have eq94425 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq94164
       grind)
    | exact superpose eq94164 eq10
    | exact resolve eq10 eq94164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94164
  have eq94701 : x = (k y x) := by
    first
    | (have i₁ := eq94425
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq94425
    | exact resolve eq94425 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94425
  have eq95013 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10731 y x
       have i₂ := eq94701
       grind)
    | exact superpose eq94701 eq10731
    | (have j0 := eq10731 y x
       grind)
    | (have r₁ := eq10731 y x
       have r₂ := eq94701
       grind)
    | exact resolve eq10731 eq94701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10731 eq94701
  have eq95096 : x = (M.op x y) := by grind
  clear eq95013
  have eq95118 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq94152
       have i₂ := eq95096
       grind)
    | exact superpose eq95096 eq94152
    | exact resolve eq94152 eq95096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94152 eq95096
  have eq95130 : False := by grind
  exact eq95130

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation2503 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq119 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq121 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq602 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq121 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq121 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq121 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq13 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq618 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq602 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq619 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq618 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq759 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq2127 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq619
    | exact resolve eq619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq2178 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2127 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2127
    | (have j0 := eq2127 X0 X1
       grind)
    | exact resolve eq2127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2217 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2178 X1 X0
       grind)
    | exact superpose eq2178 eq10
    | (have j1 := eq2178 X1 X0
       grind)
    | exact resolve eq10 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2259 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2217 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2217
    | (have j0 := eq2217 X0 X1
       grind)
    | exact resolve eq2217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2297 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq2259 X0 (σ X1)
       grind)
    | exact superpose eq2259 eq37
    | (have j1 := eq2259 X0 (σ X1)
       grind)
    | exact resolve eq37 eq2259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2259
  have eq3965 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2297 (σ X0) X1
       grind)
    | exact superpose eq2297 eq28
    | (have j1 := eq2297 (σ X0) X1
       grind)
    | exact resolve eq28 eq2297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2297
  have eq4026 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3965 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3965
    | (have j0 := eq3965 X0 X1
       grind)
    | exact resolve eq3965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965
  have eq4060 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4026 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4026
    | (have j0 := eq4026 X0 X1
       grind)
    | exact resolve eq4026 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026
  have eq4070 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4060 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4060
    | (have j0 := eq4060 X0 X1
       grind)
    | exact resolve eq4060 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq4270 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4070 X1 X0
       grind)
    | exact superpose eq4070 eq11
    | (have j1 := eq4070 X1 X0
       grind)
    | exact resolve eq11 eq4070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4070
  have eq5129 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4270 y x
       grind)
    | exact superpose eq4270 eq16
    | (have j1 := eq4270 y x
       grind)
    | exact resolve eq16 eq4270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4270
  have eq5155 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5129
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5129
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5129
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5129
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5129 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5156 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5129
       have i₂ := eq2178 y x
       grind)
    | exact superpose eq2178 eq5129
    | (have j1 := eq2178 y x
       grind)
    | (have r₁ := eq5129
       have r₂ := eq2178 y x
       grind)
    | (have r₁ := eq5129
       have r₂ := eq2178 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5129
       have r₂ := eq2178 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5129 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178 eq5129
  have eq5159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5156
  have eq5160 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq5159
  have eq5161 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5155
  have eq5162 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq5161
  have eq5166 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5160
       grind)
    | exact superpose eq5160 eq16
    | exact resolve eq16 eq5160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160
  have eq5167 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5166
       have r₂ := eq22 x
       grind)
    | exact resolve eq5166 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5166
  have eq5173 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq759 x y
       have i₂ := eq5167
       grind)
    | exact superpose eq5167 eq759
    | (have j0 := eq759 x y
       grind)
    | exact resolve eq759 eq5167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq5167
  have eq5178 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5173
  have eq5179 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5178
  have eq5183 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5162
       grind)
    | exact superpose eq5162 eq16
    | exact resolve eq16 eq5162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5162
  have eq5184 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5183
       have r₂ := eq22 x
       grind)
    | exact resolve eq5183 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5183
  have eq5193 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5179
       grind)
    | exact superpose eq5179 eq16
    | exact resolve eq16 eq5179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5179
  have eq5214 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5193
       have i₂ := eq5184
       grind)
    | exact superpose eq5184 eq5193
    | exact resolve eq5193 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5184 eq5193
  have eq5215 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq5214
  have eq5216 : (σ x) = (σ y) := by grind
  clear eq5215
  have eq5217 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5216
       grind)
    | exact superpose eq5216 eq16
    | exact resolve eq16 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5218 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5216
       grind)
    | exact superpose eq5216 eq10
    | exact resolve eq10 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5270 : x = y := by
    first
    | (have i₁ := eq5218
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5218
    | exact resolve eq5218 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5218
  have eq5271 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5217
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5217
    | exact resolve eq5217 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5217
  have eq5272 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5271
       have i₂ := eq5270
       grind)
    | exact superpose eq5270 eq5271
    | exact resolve eq5271 eq5270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5270 eq5271
  have eq5273 : False := by grind
  exact eq5273

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq458 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq469 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq469
    | exact resolve eq469 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq475 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq458 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq458
    | exact resolve eq458 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq481 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq472 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq472
    | (have j0 := eq472 x y
       grind)
    | exact resolve eq472 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq472
    | (have j0 := eq472 (σ x) (σ y)
       grind)
    | exact resolve eq472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq481 eq14
    | exact resolve eq14 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq3254 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq475 X0 X0 x
       grind)
    | exact superpose eq475 eq53
    | exact resolve eq53 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3295 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq475 X0 X0 X0
       have i₂ := eq3254 X0
       grind)
    | exact superpose eq3254 eq475
    | exact resolve eq475 eq3254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq3254
  have eq3457 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq3470 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3457 X0
       have i₂ := eq3295 X0
       grind)
    | exact superpose eq3295 eq3457
    | exact resolve eq3457 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295 eq3457
  have eq13578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13578
    | exact resolve eq13578 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13578
  have eq13590 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13579
       have r₂ := eq28
       grind)
    | exact resolve eq13579 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13579
  have eq13592 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13590
    | exact resolve eq13590 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13590
  have eq13600 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq13592
  have eq13620 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13600
    | exact resolve eq13600 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13600
  have eq16963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13620 eq111
    | exact resolve eq111 eq13620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13620
  have eq16979 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16963
  have eq16982 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16979
       have r₂ := eq28
       grind)
    | exact resolve eq16979 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16979
  have eq16991 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16982
  have eq17016 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16991
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16991
    | exact resolve eq16991 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16991
  have eq17223 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq17016
       grind)
    | exact superpose eq17016 eq70
    | exact resolve eq70 eq17016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq17016
  have eq17249 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq17223
    | exact resolve eq17223 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17223
  have eq17529 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17249 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq17249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17529
    | exact resolve eq17529 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17529
  have eq17549 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17538
       have r₂ := eq28
       grind)
    | exact resolve eq17538 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17538
  have eq17551 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17549
    | exact resolve eq17549 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17549
  have eq17552 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17551
  have eq17662 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17552
  have eq17690 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17662
    | exact resolve eq17662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17662
  have eq17801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17690 eq17249
    | exact resolve eq17249 eq17690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17249 eq17690
  have eq17809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17801
  have eq17815 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17809
       have r₂ := eq28
       grind)
    | exact resolve eq17809 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17809
  have eq17820 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17815 eq52
    | exact resolve eq52 eq17815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq17829 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17815 eq483
    | exact resolve eq483 eq17815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17851 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17820 X0
       have i₂ := eq472 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq17820 x
       have i₂ := eq472 sF2 x
       grind)
    | exact superpose eq472 eq17820
    | exact resolve eq17820 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17820
  have eq18275 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17829 eq17851
    | exact resolve eq17851 eq17829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17829 eq17851
  have eq18333 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18275
  have eq18352 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18333
    | exact resolve eq18333 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18333
  have eq18362 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18352 eq28
    | exact resolve eq28 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18385 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18352 eq17815
    | exact resolve eq17815 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17815
  have eq18388 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq18385
  have eq18396 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18388 eq27
    | exact resolve eq27 eq18388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18397 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18388 eq30
    | exact resolve eq30 eq18388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18388
  have eq18563 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq18397
    | exact resolve eq18397 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18397
  have eq19919 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18396
  have eq19958 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq483 eq19919
    | exact resolve eq19919 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq19919
  have eq20759 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18352 eq19958
    | exact resolve eq19958 eq18352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18352 eq19958
  have eq20776 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20759
  have eq21290 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20776 eq111
    | exact resolve eq111 eq20776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq20776
  have eq21311 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq21290
  have eq21325 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21311
       have r₂ := eq18362
       grind)
    | exact resolve eq21311 eq18362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18362 eq21311
  have eq22149 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq472 x x
       have i₂ := eq21325
       grind)
    | exact superpose eq21325 eq472
    | exact resolve eq472 eq21325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21325
  have eq22159 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22149
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22149
    | exact resolve eq22149 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22149
  have eq22240 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq22159
  have eq22242 : x = (M.op x y) := by
    first
    | (have r₁ := eq22240
       have r₂ := eq18563
       grind)
    | exact resolve eq22240 eq18563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18563 eq22240
  have eq22304 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq22242 eq21
    | exact resolve eq21 eq22242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq22370 : x = (M.op x x) := by
    first
    | exact superpose eq22242 eq481
    | exact resolve eq481 eq22242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq22371 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq22242 eq499
    | exact resolve eq499 eq22242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq22385 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq22371 X0
       have i₂ := eq472 x X0
       grind)
    | (have i₁ := eq22371 X0
       have i₂ := eq472 x (M.op x X0)
       grind)
    | exact superpose eq472 eq22371
    | exact resolve eq22371 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq22371
  have eq22447 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22304
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22304
    | exact resolve eq22304 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22304
  have eq22641 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq22447 eq27
    | exact resolve eq27 eq22447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22809 : x = (k x x) := by
    first
    | (have i₁ := eq3470 x
       have i₂ := eq22370
       grind)
    | exact superpose eq22370 eq3470
    | exact resolve eq3470 eq22370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3470
  have eq22959 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq604 x x
       have i₂ := eq22809
       grind)
    | exact superpose eq22809 eq604
    | (have j0 := eq604 x x
       grind)
    | exact resolve eq604 eq22809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq22809
  have eq22962 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22959
  have eq22963 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22962
  have eq22974 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22963
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22963
    | exact resolve eq22963 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22963
  have eq22990 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22447 eq22974
    | exact resolve eq22974 eq22447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22974
  have eq23191 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq22385 X0
       grind)
    | exact superpose eq22385 eq14
    | exact resolve eq14 eq22385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22385
  have eq23248 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23191 X0
       have i₂ := eq22370
       grind)
    | exact superpose eq22370 eq23191
    | exact resolve eq23191 eq22370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22370 eq23191
  have eq23280 : y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq23248 y
       grind)
    | exact superpose eq23248 eq19
    | (have j1 := eq23248 y
       grind)
    | exact resolve eq19 eq23248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq23248
  have eq23381 : x = y := by
    first
    | exact superpose eq22242 eq23280
    | exact resolve eq23280 eq22242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22242 eq23280
  have eq23446 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq23381
       grind)
    | exact superpose eq23381 eq25
    | exact resolve eq25 eq23381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq23381
  have eq23584 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq23446
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23446
    | exact resolve eq23446 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq23446
  have eq23648 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22447 eq23584
    | exact resolve eq23584 eq22447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22447 eq23584
  have eq23887 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23648 eq22641
    | exact resolve eq22641 eq23648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22641 eq23648
  have eq23891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22990 eq23887
    | exact resolve eq23887 eq22990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22990 eq23887
  have eq23956 : False := by grind
  exact eq23956

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyy_pxx_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq36 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq42 X0 X1 X2 X3
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq42 X0 X1 X2 X3
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq72 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq69 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq69
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq204 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq42 X0 X0 x X0
       have i₂ := eq75 X0 X0 x
       grind)
    | exact superpose eq75 eq42
    | exact resolve eq42 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq215 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0 X0 X0
       have i₂ := eq204 X0
       grind)
    | exact superpose eq204 eq75
    | exact resolve eq75 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq204
  have eq247 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq252 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq9
    | exact resolve eq9 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq74 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq252 X0 X1
       have i₂ := eq74 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq74 eq252
    | exact resolve eq252 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq252
  have eq302 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq215 x y
       grind)
    | exact superpose eq215 eq16
    | (have j1 := eq215 y y
       grind)
    | exact resolve eq16 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq215 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq317 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq316 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq344 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq254 X0 X1
       grind)
    | exact superpose eq254 eq9
    | exact resolve eq9 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq344
    | exact resolve eq344 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq359 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X1 X0
       have i₂ := eq352 X1 X0
       grind)
    | exact superpose eq352 eq254
    | exact resolve eq254 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq362 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq352 X1 X0
       grind)
    | exact superpose eq352 eq9
    | exact resolve eq9 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq317 (M.op X0 X0)
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq317
    | (have j0 := eq317 (M.op X0 X0)
       grind)
    | exact resolve eq317 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq317 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq317
    | (have j0 := eq317 (τ X0)
       grind)
    | exact resolve eq317 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq317
  have eq461 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq452 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq467 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq456 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq456
    | (have j0 := eq456 X0
       grind)
    | exact resolve eq456 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq474 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq467 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq467
    | (have j0 := eq467 X0
       grind)
    | exact resolve eq467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq481 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq474 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq474
    | (have j0 := eq474 (τ X0)
       grind)
    | exact resolve eq474 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq723 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq352 (σ (M.op X0 X0)) X1
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq352
    | exact resolve eq352 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 (σ (M.op X0 X0))
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq359
    | exact resolve eq359 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq1762 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq302
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq302
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq302 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq1763 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq1762
  have eq2926 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq481 (M.op X0 X0)
       have i₂ := eq247 X0
       grind)
    | exact superpose eq247 eq481
    | (have j0 := eq481 (M.op X0 X0)
       grind)
    | exact resolve eq481 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq481
  have eq2935 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq38059 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq1763
       grind)
    | exact superpose eq1763 eq36
    | exact resolve eq36 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1763
  have eq38211 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38059
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq38059
    | exact resolve eq38059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38059
  have eq38215 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq474 y
       grind)
    | (have r₁ := eq38211
       have r₂ := eq474 y
       grind)
    | exact resolve eq38211 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq38211
  have eq1436391 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2935 (σ y)
       have i₂ := eq38215
       grind)
    | exact superpose eq38215 eq2935
    | exact resolve eq2935 eq38215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935 eq38215
  have eq1437069 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1436391
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1436391
    | exact resolve eq1436391 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436391
  have eq1440198 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq352 y X0
       have i₂ := eq1437069
       grind)
    | exact superpose eq1437069 eq352
    | exact resolve eq352 eq1437069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq1437069
  have eq1444682 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq233 y
       have i₂ := eq1440198 X0
       grind)
    | exact superpose eq1440198 eq233
    | (have j1 := eq1440198 X0
       grind)
    | exact resolve eq233 eq1440198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq1440198
  have eq1445236 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1444682 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444682
  have eq1445277 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 x
       have i₂ := eq1445236 X0
       grind)
    | exact superpose eq1445236 eq359
    | (have j1 := eq1445236 X1
       grind)
    | exact resolve eq359 eq1445236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1445281 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq723 x X0
       have i₂ := eq1445236 X1
       grind)
    | exact superpose eq1445236 eq723
    | (have j1 := eq1445236 X1
       grind)
    | exact resolve eq723 eq1445236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq1445236
  have eq1452069 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq1445277 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445277
  have eq1452070 : x = (M.op y x) := by grind
  clear eq1452069
  have eq1452211 : y = (M.op x y) := by
    first
    | (have i₁ := eq362 x y
       have i₂ := eq1452070
       grind)
    | exact superpose eq1452070 eq362
    | exact resolve eq362 eq1452070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq1452070
  have eq1544934 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1445281 (σ y) X0
       grind)
    | exact superpose eq1445281 eq16
    | (have j1 := eq1445281 X0 X0
       grind)
    | exact resolve eq16 eq1445281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445281
  have eq1546464 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1544934 X0
       have i₂ := eq1452211
       grind)
    | exact superpose eq1452211 eq1544934
    | (have j0 := eq1544934 X0
       grind)
    | exact resolve eq1544934 eq1452211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452211 eq1544934
  have eq1546465 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1546464 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546464
  have eq1546521 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq359 X0 y
       have i₂ := eq1546465 y
       grind)
    | exact superpose eq1546465 eq359
    | exact resolve eq359 eq1546465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq1546526 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq724 y x
       have i₂ := eq1546465 y
       grind)
    | exact superpose eq1546465 eq724
    | exact resolve eq724 eq1546465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq1546465
  have eq1563533 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1546526 (σ x)
       grind)
    | exact superpose eq1546526 eq16
    | exact resolve eq16 eq1546526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546526
  have eq1564090 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1563533
       have i₂ := eq1546521 x
       grind)
    | exact superpose eq1546521 eq1563533
    | exact resolve eq1563533 eq1546521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546521 eq1563533
  have eq1564091 : False := by grind
  exact eq1564091

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxx_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq109
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq381 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq394 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq394
    | exact resolve eq394 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq399 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq381 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq381
    | exact resolve eq381 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq500 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq65 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3447 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 X0 X0 x X0
       have i₂ := eq399 X0 X0 x
       grind)
    | exact superpose eq399 eq54
    | exact resolve eq54 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3483 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq399 X0 X0 X0
       have i₂ := eq3447 X0
       grind)
    | exact superpose eq3447 eq399
    | exact resolve eq399 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq3447
  have eq3499 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq3483
  have eq3547 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq3572 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3547 X0
       have i₂ := eq3499 X0
       grind)
    | exact superpose eq3499 eq3547
    | exact resolve eq3547 eq3499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq14471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq14471
    | exact resolve eq14471 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14471
  have eq14483 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14472
       have r₂ := eq29
       grind)
    | exact resolve eq14472 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14472
  have eq14497 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq14483 eq3499
    | exact resolve eq3499 eq14483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14515 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq14483 eq396
    | exact resolve eq396 eq14483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14483
  have eq14525 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq14515
    | exact resolve eq14515 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14515
  have eq14539 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3499 x
       have i₂ := eq14525
       grind)
    | exact superpose eq14525 eq3499
    | exact resolve eq3499 eq14525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14525
  have eq15131 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq14539
       grind)
    | exact superpose eq14539 eq75
    | exact resolve eq75 eq14539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq14539
  have eq15153 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15131
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq15131
    | exact resolve eq15131 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15131
  have eq15582 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15153 eq11
    | (have j0 := eq11 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq15153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15153
  have eq15583 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15582
  have eq15587 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq15583
    | exact resolve eq15583 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15583
  have eq15588 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq15587
  have eq16228 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq15588 eq396
    | exact resolve eq396 eq15588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15588
  have eq16238 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq16228
    | exact resolve eq16228 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16228
  have eq16239 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16238
  have eq16240 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16239 eq29
    | exact resolve eq29 eq16239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16239
  have eq19048 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq14497 eq110
    | exact resolve eq110 eq14497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq14497
  have eq19060 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq19048
  have eq19069 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19060
       have r₂ := eq16240
       grind)
    | exact resolve eq19060 eq16240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19060
  have eq19107 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq396 x x
       have i₂ := eq19069
       grind)
    | exact superpose eq19069 eq396
    | exact resolve eq396 eq19069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq19069
  have eq19118 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19107
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq19107
    | exact resolve eq19107 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19107
  have eq19121 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19118 eq31
    | exact resolve eq31 eq19118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19118
  have eq19241 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq19121
    | exact resolve eq19121 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19121
  have eq19242 : y = (M.op x y) ∨ x = y := by grind
  clear eq19241
  have eq19361 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq19242 eq22
    | exact resolve eq22 eq19242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19499 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19361
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq19361
    | exact resolve eq19361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19361
  have eq19572 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq19499 eq16240
    | (have r₁ := eq16240
       have r₂ := eq19499
       grind)
    | exact resolve eq16240 eq19499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16240 eq19499
  have eq19629 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq19572
  have eq19630 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq19629
  have eq19700 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq19630 eq30
    | exact resolve eq30 eq19630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19630
  have eq19877 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq19700
    | exact resolve eq19700 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq19700
  have eq20076 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq19877 eq19242
    | exact resolve eq19242 eq19877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19242 eq19877
  have eq20077 : x = y := by grind
  clear eq20076
  have eq20146 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq20077
       grind)
    | exact superpose eq20077 eq20
    | exact resolve eq20 eq20077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq20147 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq20077
       grind)
    | exact superpose eq20077 eq26
    | exact resolve eq26 eq20077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq20077
  have eq20263 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20147
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20147
    | exact resolve eq20147 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20147
  have eq20267 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20263 eq28
    | exact resolve eq28 eq20263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20263
  have eq20395 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq20146
       grind)
    | exact superpose eq20146 eq67
    | exact resolve eq67 eq20146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq20409 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3572 x
       have i₂ := eq20146
       grind)
    | exact superpose eq20146 eq3572
    | exact resolve eq3572 eq20146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3572 eq20146
  have eq20438 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq20395
    | exact resolve eq20395 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20395
  have eq20458 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq20267 eq3499
    | exact resolve eq3499 eq20267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3499
  have eq20555 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20409 eq500
    | (have j0 := eq500 (M.op x y)
       grind)
    | exact resolve eq500 eq20409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq20409
  have eq20560 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq20555
  have eq20563 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq20560
    | exact resolve eq20560 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20560
  have eq22045 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq22055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20267 eq22045
    | exact resolve eq22045 eq20267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22045
  have eq22068 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22055
       have r₂ := eq29
       grind)
    | exact resolve eq22055 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22055
  have eq22075 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20267 eq22068
    | exact resolve eq22068 eq20267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22068
  have eq22082 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22075 eq29
    | exact resolve eq29 eq22075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22125 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22075 eq20458
    | exact resolve eq20458 eq22075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20458 eq22075
  have eq23191 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22125 eq20438
    | exact resolve eq20438 eq22125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20438 eq22125
  have eq23202 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq23191
  have eq23212 : x = (M.op x y) := by
    first
    | (have r₁ := eq23202
       have r₂ := eq22082
       grind)
    | exact resolve eq23202 eq22082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22082 eq23202
  have eq23230 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23212 eq22
    | exact resolve eq22 eq23212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23212
  have eq23383 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23230
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23230
    | exact resolve eq23230 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq23230
  have eq23580 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23383 eq20267
    | exact resolve eq20267 eq23383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20267 eq23383
  have eq23587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20563 eq23580
    | exact resolve eq23580 eq20563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20563 eq23580
  have eq23651 : False := by grind
  exact eq23651

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq66 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq88
    | exact resolve eq88 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq94
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq345 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq50 X0 X1 X2 X3
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq50 X0 X1 X2 X3
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq354 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq354
    | exact resolve eq354 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq359 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq345 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq345
    | exact resolve eq345 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq438 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq3296 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0 X0 x X0
       have i₂ := eq359 X0 X0 x
       grind)
    | exact superpose eq359 eq50
    | exact resolve eq50 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq3331 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq359 X0 X0 X0
       have i₂ := eq3296 X0
       grind)
    | exact superpose eq3296 eq359
    | exact resolve eq359 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq3296
  have eq3495 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  clear eq3331
  have eq12462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq12462
    | exact resolve eq12462 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12462
  have eq12474 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12463
       have r₂ := eq29
       grind)
    | exact resolve eq12463 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12463
  have eq12482 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  have eq12496 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq12474 eq356
    | exact resolve eq356 eq12474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12474
  have eq12499 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq12496
    | exact resolve eq12496 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12496
  have eq12507 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12499
  have eq12829 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq12507
       grind)
    | exact superpose eq12507 eq83
    | exact resolve eq83 eq12507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq12507
  have eq12851 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12829
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq12829
    | exact resolve eq12829 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12829
  have eq13348 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12851 eq11
    | (have j0 := eq11 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq12851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12851
  have eq13349 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13348
  have eq13353 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq13349
    | exact resolve eq13349 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13349
  have eq13354 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq13353
  have eq13657 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq13354 eq356
    | exact resolve eq356 eq13354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13354
  have eq13660 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq13657
    | exact resolve eq13657 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13657
  have eq13661 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13660
  have eq13662 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13661 eq29
    | exact resolve eq29 eq13661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13661
  have eq14329 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq12482 eq95
    | exact resolve eq95 eq12482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq12482
  have eq14341 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq14329
  have eq14350 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14341
       have r₂ := eq13662
       grind)
    | exact resolve eq14341 eq13662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14341
  have eq14376 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq356 x x
       have i₂ := eq14350
       grind)
    | exact superpose eq14350 eq356
    | exact resolve eq356 eq14350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq14350
  have eq14380 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14376
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14376
    | exact resolve eq14376 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14376
  have eq14504 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq14380 eq31
    | exact resolve eq31 eq14380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14380
  have eq14624 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq14504
    | exact resolve eq14504 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14504
  have eq14625 : y = (M.op x y) ∨ x = y := by grind
  clear eq14624
  have eq14626 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14625 eq22
    | exact resolve eq22 eq14625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14743 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14626
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq14626
    | exact resolve eq14626 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14626
  have eq14817 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14743 eq13662
    | (have r₁ := eq13662
       have r₂ := eq14743
       grind)
    | exact resolve eq13662 eq14743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13662 eq14743
  have eq14828 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq14817
  have eq14829 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq14828
  have eq14901 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq14829 eq30
    | exact resolve eq30 eq14829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14829
  have eq15043 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq14901
    | exact resolve eq14901 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq14901
  have eq15111 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15043 eq14625
    | exact resolve eq14625 eq15043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14625 eq15043
  have eq15112 : x = y := by grind
  clear eq15111
  have eq15172 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq15112
       grind)
    | exact superpose eq15112 eq20
    | exact resolve eq20 eq15112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq15173 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq15112
       grind)
    | exact superpose eq15112 eq26
    | exact resolve eq26 eq15112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15112
  have eq15279 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15173
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15173
    | exact resolve eq15173 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15173
  have eq15282 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15279 eq28
    | exact resolve eq28 eq15279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15279
  have eq15410 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq15172
       grind)
    | exact superpose eq15172 eq66
    | exact resolve eq66 eq15172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq15413 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3495 x
       have i₂ := eq15172
       grind)
    | exact superpose eq15172 eq3495
    | exact resolve eq3495 eq15172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15172
  have eq15435 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq15410
    | exact resolve eq15410 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15410
  have eq15445 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15282 eq3495
    | exact resolve eq3495 eq15282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3495
  have eq15483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15413 eq438
    | (have j0 := eq438 (M.op x y)
       grind)
    | exact resolve eq438 eq15413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq15413
  have eq15487 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq15483
  have eq15491 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq15487
    | exact resolve eq15487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15487
  have eq18473 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq18481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15282 eq18473
    | exact resolve eq18473 eq15282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18473
  have eq18493 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18481
       have r₂ := eq29
       grind)
    | exact resolve eq18481 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18481
  have eq18500 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15282 eq18493
    | exact resolve eq18493 eq15282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18493
  have eq18506 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18500 eq29
    | exact resolve eq29 eq18500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18525 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18500 eq15445
    | exact resolve eq15445 eq18500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15445 eq18500
  have eq19407 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18525 eq15435
    | exact resolve eq15435 eq18525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15435 eq18525
  have eq19418 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq19407
  have eq19430 : x = (M.op x y) := by
    first
    | (have r₁ := eq19418
       have r₂ := eq18506
       grind)
    | exact resolve eq19418 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18506 eq19418
  have eq19448 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19430 eq22
    | exact resolve eq22 eq19430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19430
  have eq19588 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19448
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19448
    | exact resolve eq19448 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19448
  have eq19758 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19588 eq15282
    | exact resolve eq15282 eq19588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15282 eq19588
  have eq19766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15491 eq19758
    | exact resolve eq19758 eq15491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15491 eq19758
  have eq19830 : False := by grind
  exact eq19830

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
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
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq337 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x X0 X1 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq351 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq351
    | exact resolve eq351 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq354 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq344
    | (have j0 := eq344 X0 X1
       grind)
    | exact resolve eq344 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq356 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq342 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq342
    | exact resolve eq342 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq372 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq353 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq353
    | (have j0 := eq353 x y
       grind)
    | exact resolve eq353 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq353
    | (have j0 := eq353 (σ x) (σ y)
       grind)
    | exact resolve eq353 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq87 X0 X0
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq87 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq458 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq453 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq460 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq458 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq458 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq458 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq2969 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq354 eq52
    | exact resolve eq52 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2979 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2969 eq354
    | exact resolve eq354 eq2969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq2969
  have eq2990 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2979 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       have r₂ := eq2979
       grind)
    | exact resolve eq13 eq2979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2995 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq2990 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990
  have eq3110 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq356 X0 X0 x
       grind)
    | exact superpose eq356 eq52
    | exact resolve eq52 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3141 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq345 x x
       have i₂ := eq3110 x
       grind)
    | exact superpose eq3110 eq345
    | exact resolve eq345 eq3110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq3142 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq346 sF2 sF2
       have i₂ := eq3110 sF2
       grind)
    | exact superpose eq3110 eq346
    | exact resolve eq346 eq3110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq3110
  have eq3229 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq2995 eq460
    | (have j0 := eq460 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq460 eq2995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq3244 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq2979 eq3229
    | (have j0 := eq3229 X0
       grind)
    | exact resolve eq3229 eq2979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979 eq3229
  have eq3245 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq3244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3244
  have eq3287 : (M.op (σ x) (σ x)) = (σ (k x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq3245 eq35
    | exact resolve eq35 eq3245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3288 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq3245 eq36
    | exact resolve eq36 eq3245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3245
  have eq3311 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq2995 eq3288
    | exact resolve eq3288 eq2995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288
  have eq3312 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq2995 eq3287
    | exact resolve eq3287 eq2995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995 eq3287
  have eq3328 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3311
       grind)
    | exact superpose eq3311 eq16
    | exact resolve eq16 eq3311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3364 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3312
       grind)
    | exact superpose eq3312 eq16
    | exact resolve eq16 eq3312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3541 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq337 X0 X0 x X0 X2
       have i₂ := eq356 X0 X0 x
       grind)
    | exact superpose eq356 eq337
    | exact resolve eq337 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq40798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq40799 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq40798
    | exact resolve eq40798 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40798
  have eq40811 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq40799
       have r₂ := eq27
       grind)
    | exact resolve eq40799 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40799
  have eq40816 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40811 eq3328
    | exact resolve eq3328 eq40811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328 eq40811
  have eq40933 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq40816
    | exact resolve eq40816 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40816
  have eq40934 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq40933
  have eq40948 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40934 eq3364
    | exact resolve eq3364 eq40934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364 eq40934
  have eq41061 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq40948
    | exact resolve eq40948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq40948
  have eq41062 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq41061
  have eq41075 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3311
       have i₂ := eq41062
       grind)
    | exact superpose eq41062 eq3311
    | exact resolve eq3311 eq41062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq41148 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq356 y y x
       have i₂ := eq41062
       grind)
    | exact superpose eq41062 eq356
    | exact resolve eq356 eq41062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41152 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq41148 X0
       have i₂ := eq353 y X0
       grind)
    | (have i₁ := eq41148 X0
       have i₂ := eq353 y (M.op y X0)
       grind)
    | exact superpose eq353 eq41148
    | exact resolve eq41148 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41148
  have eq41193 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41075
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41075
    | exact resolve eq41075 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41075
  have eq41278 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq41193 eq356
    | exact resolve eq356 eq41193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq41282 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq41278 X0
       have i₂ := eq353 sF3 (M.op sF3 X0)
       grind)
    | (have i₁ := eq41278 x
       have i₂ := eq353 sF3 x
       grind)
    | exact superpose eq353 eq41278
    | exact resolve eq41278 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41278
  have eq41919 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq41152 X0
       grind)
    | exact superpose eq41152 eq14
    | exact resolve eq14 eq41152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41152
  have eq43532 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq41282 eq14
    | exact resolve eq14 eq41282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41282
  have eq44201 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq41919 X0
       have i₂ := eq41062
       grind)
    | exact superpose eq41062 eq41919
    | exact resolve eq41919 eq41062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41062 eq41919
  have eq44311 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq44201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44201
  have eq44316 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3141
       have i₂ := eq44311 X0
       grind)
    | exact superpose eq44311 eq3141
    | (have j1 := eq44311 X0
       grind)
    | exact resolve eq3141 eq44311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3141
  have eq44432 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq372 eq44316
    | (have j0 := eq44316 X0
       grind)
    | exact resolve eq44316 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq44316
  have eq44565 : ∀ X0 : G, y = (M.op (M.op x x) y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq44432 (M.op sF0 X0)
       grind)
    | exact superpose eq44432 eq50
    | (have j1 := eq44432 X0
       grind)
    | exact resolve eq50 eq44432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq44432
  have eq44736 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq41193 eq43532
    | exact resolve eq43532 eq41193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44848 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq44736 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44736
  have eq44854 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3312
       have i₂ := eq44848 X0
       grind)
    | exact superpose eq44848 eq3312
    | (have j1 := eq44848 X0
       grind)
    | exact resolve eq3312 eq44848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44848
  have eq44968 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44854 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44854
    | (have j0 := eq44854 X0
       grind)
    | exact resolve eq44854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44854
  have eq44978 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3142
       have i₂ := eq44968 (M.op sF2 sF2)
       grind)
    | exact superpose eq44968 eq3142
    | (have j1 := eq44968 X0
       grind)
    | exact resolve eq3142 eq44968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3142 eq44968
  have eq45093 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq374 eq44978
    | (have j0 := eq44978 X0
       grind)
    | exact resolve eq44978 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq44978
  have eq45186 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0
       have i₂ := eq45093 (M.op sF4 X0)
       grind)
    | exact superpose eq45093 eq51
    | (have j1 := eq45093 X0
       grind)
    | exact resolve eq51 eq45093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq45093
  have eq47364 : ∀ X0 X1 : G, y = (M.op x y) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44565 X0
       have i₂ := eq44311 X1
       grind)
    | exact superpose eq44311 eq44565
    | (have j0 := eq44565 X0
       have j1 := eq44311 X0
       grind)
    | exact resolve eq44565 eq44311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44311 eq44565
  have eq47403 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq47364 X1 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47364
    | (have j0 := eq47364 X1 X1
       grind)
    | exact resolve eq47364 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47364
  have eq90623 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq47403 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47403
  have eq90624 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq90623 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90623
  have eq90673 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3541 y X0
       have i₂ := eq90624 y
       grind)
    | exact superpose eq90624 eq3541
    | exact resolve eq3541 eq90624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90788 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90673 X0
       have i₂ := eq353 y X0
       grind)
    | (have i₁ := eq90673 X0
       have i₂ := eq353 y (M.op y X0)
       grind)
    | exact superpose eq353 eq90673
    | exact resolve eq90673 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq90673
  have eq93193 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90788 X0
       have i₂ := eq90624 X0
       grind)
    | exact superpose eq90624 eq90788
    | exact resolve eq90788 eq90624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90624 eq90788
  have eq93236 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq93193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93193
  have eq93334 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq93236 x
       grind)
    | exact superpose eq93236 eq18
    | (have j1 := eq93236 x
       grind)
    | exact resolve eq18 eq93236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq93236
  have eq93394 : y = (M.op x y) := by grind
  clear eq93334
  have eq93818 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq93394 eq20
    | exact resolve eq20 eq93394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq93394
  have eq94075 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq93818
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93818
    | exact resolve eq93818 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq93818
  have eq94130 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq94075 eq26
    | exact resolve eq26 eq94075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94205 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq94075 eq41193
    | exact resolve eq41193 eq94075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41193
  have eq94213 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq94075 eq43532
    | exact resolve eq43532 eq94075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43532
  have eq108915 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq94205 eq94213
    | exact resolve eq94213 eq94205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94205 eq94213
  have eq109071 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq108915 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108915
  have eq109099 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3312
       have i₂ := eq109071 X0
       grind)
    | exact superpose eq109071 eq3312
    | (have j1 := eq109071 X0
       grind)
    | exact resolve eq3312 eq109071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3312 eq109071
  have eq109262 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109099 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq109099
    | (have j0 := eq109099 X0
       grind)
    | exact resolve eq109099 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq109099
  have eq109601 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45186 X0
       have i₂ := eq109262 (M.op sF2 sF2)
       grind)
    | exact superpose eq109262 eq45186
    | (have j0 := eq45186 X0
       have j1 := eq109262 X1
       grind)
    | exact resolve eq45186 eq109262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45186 eq109262
  have eq109721 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq26 eq109601
    | (have j0 := eq109601 X0 X1
       grind)
    | exact resolve eq109601 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq109601
  have eq109738 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq94075 eq109721
    | (have j0 := eq109721 X0 X1
       grind)
    | exact resolve eq109721 eq94075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109721
  have eq109744 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ (M.op (σ (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq109738 X0 X1
       grind)
    | (have r₁ := eq109738 X0 X1
       have r₂ := eq27
       grind)
    | exact resolve eq109738 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109738
  have eq109747 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X1) = X1 ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq94075 eq109744
    | (have j0 := eq109744 X0 X1
       grind)
    | exact resolve eq109744 eq94075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94075 eq109744
  have eq110370 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq109747 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109747
  have eq110371 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq110370 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110370
  have eq110520 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq110371 eq3541
    | exact resolve eq3541 eq110371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3541
  have eq110594 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq110371 eq110520
    | exact resolve eq110520 eq110371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110520
  have eq110643 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq110371 eq110594
    | exact resolve eq110594 eq110371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110371 eq110594
  have eq110828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq110643 eq94130
    | exact resolve eq94130 eq110643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94130 eq110643
  have eq110877 : False := by grind
  exact eq110877
