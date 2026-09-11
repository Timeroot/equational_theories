import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation842 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq94 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq151 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq159 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq160 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq159 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq165 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq160
    | (have j0 := eq160 X0 X1
       grind)
    | exact resolve eq160 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq166 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq165 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq369 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq166 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq166
    | exact resolve eq166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq166 x y
       grind)
    | exact superpose eq166 eq16
    | (have j1 := eq166 x y
       grind)
    | exact resolve eq16 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq387 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq369
    | (have j0 := eq369 X0 X1
       grind)
    | exact resolve eq369 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq369
  have eq429 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq387
    | exact resolve eq387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq535 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq375
       have i₂ := eq429 x y
       grind)
    | exact superpose eq429 eq375
    | (have j1 := eq429 (σ x) (σ y)
       grind)
    | (have r₁ := eq375
       have r₂ := eq429 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq375
       have r₂ := eq429 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq375 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq429
  have eq538 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq535
  have eq562 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq538
       grind)
    | exact superpose eq538 eq10
    | exact resolve eq10 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq596 : x = y ∨ x = y := by
    first
    | (have i₁ := eq562
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq562
    | exact resolve eq562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq597 : x = y := by grind
  clear eq596
  have eq599 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq597
       grind)
    | exact superpose eq597 eq16
    | exact resolve eq16 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq600 : False := by grind
  exact eq600

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation842 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
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
  have eq205 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq207 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq1220 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq205 x y
       grind)
    | exact superpose eq205 eq16
    | (have j1 := eq205 x y
       grind)
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1222 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq1740 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq207 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq207
    | exact resolve eq207 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1897 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1740 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1740
    | (have j0 := eq1740 X0 X1
       grind)
    | exact resolve eq1740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq2006 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1222 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq1222
    | (have j0 := eq1222 (τ X0) (τ X1)
       grind)
    | exact resolve eq1222 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq2014 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2006 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2006
    | (have j0 := eq2006 X0 X1
       grind)
    | exact resolve eq2006 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2017 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2014 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2014
    | (have j0 := eq2014 X0 X1
       grind)
    | exact resolve eq2014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2019 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2017 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2017
    | (have j0 := eq2017 X0 X1
       grind)
    | exact resolve eq2017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq2020 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2019 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2019
    | (have j0 := eq2019 X0 X1
       grind)
    | exact resolve eq2019 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2021 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2020 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2020
    | (have j0 := eq2020 X0 X1
       grind)
    | exact resolve eq2020 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2022 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2021 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2021
    | (have j0 := eq2021 X0 X1
       grind)
    | exact resolve eq2021 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq6999 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1220
       have i₂ := eq1897 x y
       grind)
    | exact superpose eq1897 eq1220
    | (have j1 := eq1897 (σ x) (σ y)
       grind)
    | (have r₁ := eq1220
       have r₂ := eq1897 x y
       grind)
    | (have r₁ := eq1220
       have r₂ := eq1897 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1220
       have r₂ := eq1897 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1220 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq1897
  have eq7000 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq6999
  have eq7002 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq7000
       grind)
    | exact superpose eq7000 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq7000
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7000
       grind)
    | exact resolve eq13 eq7000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7000
  have eq7003 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7002
  have eq7004 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7003
  have eq7989 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7004
       grind)
    | exact superpose eq7004 eq16
    | exact resolve eq16 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7990 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq7989
       have r₂ := eq22 x
       grind)
    | exact resolve eq7989 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7989
  have eq7993 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq7990
       grind)
    | exact superpose eq7990 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7990
       grind)
    | exact resolve eq13 eq7990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7990
  have eq7994 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq7993
  have eq7995 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq7994
  have eq7997 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq7995
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7995
    | exact resolve eq7995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995
  have eq8005 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1222 x y
       have i₂ := eq7997
       grind)
    | exact superpose eq7997 eq1222
    | (have j0 := eq1222 x y
       grind)
    | (have r₁ := eq1222 x y
       have r₂ := eq7997
       grind)
    | exact resolve eq1222 eq7997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7997
  have eq8024 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq8005
  have eq8025 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq8024
  have eq8029 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1222 x y
       grind)
    | (have r₁ := eq8025
       have r₂ := eq1222 x y
       grind)
    | exact resolve eq8025 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222 eq8025
  have eq8032 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8029
       grind)
    | exact superpose eq8029 eq16
    | exact resolve eq16 eq8029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8033 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq8029
       grind)
    | exact superpose eq8029 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8029
       grind)
    | exact resolve eq13 eq8029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8029
  have eq8034 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq8033
  have eq8035 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq8034
  have eq8037 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq8035
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8035
    | exact resolve eq8035 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8035
  have eq8043 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8037
       grind)
    | exact superpose eq8037 eq10
    | exact resolve eq10 eq8037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8037
  have eq8115 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq8043
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8043
    | exact resolve eq8043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8043
  have eq8117 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8115
       grind)
    | exact superpose eq8115 eq16
    | exact resolve eq16 eq8115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8115
  have eq8118 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq8117
       have r₂ := eq22 x
       grind)
    | exact resolve eq8117 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8117
  have eq8128 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq8118
       grind)
    | exact superpose eq8118 eq10
    | exact resolve eq10 eq8118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8118
  have eq8201 : y = (k x y) := by
    first
    | (have i₁ := eq8128
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8128
    | exact resolve eq8128 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8128
  have eq8213 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2022 x y
       have i₂ := eq8201
       grind)
    | exact superpose eq8201 eq2022
    | (have j0 := eq2022 x y
       grind)
    | (have r₁ := eq2022 x y
       have r₂ := eq8201
       grind)
    | exact resolve eq2022 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022 eq8201
  have eq8225 : y = (M.op x y) ∨ x = y := by grind
  clear eq8213
  have eq8229 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8032
       have i₂ := eq8225
       grind)
    | exact superpose eq8225 eq8032
    | exact resolve eq8032 eq8225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8032 eq8225
  have eq8235 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq8229
  have eq8236 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8235
       grind)
    | exact superpose eq8235 eq16
    | exact resolve eq16 eq8235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8235
  have eq8241 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq8236
       have r₂ := eq22 x
       grind)
    | exact resolve eq8236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8236
  have eq8242 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8241
       grind)
    | exact superpose eq8241 eq16
    | exact resolve eq16 eq8241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8243 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8241
       grind)
    | exact superpose eq8241 eq10
    | exact resolve eq10 eq8241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8241
  have eq8315 : x = y := by
    first
    | (have i₁ := eq8243
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8243
    | exact resolve eq8243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8243
  have eq8316 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8242
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq8242
    | exact resolve eq8242 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8242
  have eq8317 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8316
       have i₂ := eq8315
       grind)
    | exact superpose eq8315 eq8316
    | exact resolve eq8316 eq8315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8315 eq8316
  have eq8318 : False := by grind
  exact eq8318

/-- `Equation860`: `x = x ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation860 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law860 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law860.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq295 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq299 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq301 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq295 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq302 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq300 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq300 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq300 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq314 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq302 (σ X0)
       grind)
    | exact superpose eq302 eq15
    | exact resolve eq15 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq314 X0
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq314
    | exact resolve eq314 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq314
  have eq383 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq333 X0
       grind)
    | exact superpose eq333 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq301 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq699 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq714 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq699 (σ X0) (σ X1)
       grind)
    | exact superpose eq699 eq15
    | (have j1 := eq699 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq699 (τ X0) X1
       grind)
    | exact superpose eq699 eq17
    | (have j1 := eq699 (τ X0) X1
       grind)
    | exact resolve eq17 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq699
  have eq840 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq722 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq722
    | exact resolve eq722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq906 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq840 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq840
    | (have j0 := eq840 X0 X1
       grind)
    | exact resolve eq840 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq1957 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq714 x y
       grind)
    | exact superpose eq714 eq16
    | (have j1 := eq714 x y
       grind)
    | exact resolve eq16 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1996 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq714 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq2172 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1957
       have i₂ := eq906 x y
       grind)
    | exact superpose eq906 eq1957
    | (have j1 := eq906 (σ x) (σ y)
       grind)
    | (have r₁ := eq1957
       have r₂ := eq906 x y
       grind)
    | exact resolve eq1957 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2173 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2172
  have eq2178 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2173
       grind)
    | exact superpose eq2173 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2173
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2173
       grind)
    | exact resolve eq13 eq2173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2183 : y = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2178
  have eq3516 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1996 x y
       have i₂ := eq2183
       grind)
    | exact superpose eq2183 eq1996
    | (have j0 := eq1996 x y
       grind)
    | exact resolve eq1996 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996 eq2183
  have eq3523 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq3516
  have eq3524 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq3523
  have eq3530 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3524
       grind)
    | exact superpose eq3524 eq16
    | exact resolve eq16 eq3524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3537 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3524
       grind)
    | exact superpose eq3524 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3524
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq3524
       grind)
    | exact resolve eq13 eq3524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq3545 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq3537
  have eq3549 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3545
       have i₂ := eq333 y
       grind)
    | exact superpose eq333 eq3545
    | exact resolve eq3545 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq3545
  have eq3551 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3549
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3549
    | exact resolve eq3549 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549
  have eq6357 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq906 x y
       have i₂ := eq3551
       grind)
    | exact superpose eq3551 eq906
    | (have j0 := eq906 x y
       grind)
    | exact resolve eq906 eq3551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3551
  have eq6420 : y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq6357
       have r₂ := eq3530
       grind)
    | exact resolve eq6357 eq3530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6357
  have eq6454 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3530
       have i₂ := eq6420
       grind)
    | exact superpose eq6420 eq3530
    | exact resolve eq3530 eq6420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6420
  have eq6477 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq6454
  have eq6478 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq6477
  have eq6487 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq383 y X0
       have i₂ := eq6478
       grind)
    | exact superpose eq6478 eq383
    | (have j0 := eq383 y X0
       grind)
    | (have r₁ := eq383 y x
       have r₂ := eq6478
       grind)
    | exact resolve eq383 eq6478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6478
  have eq6529 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq6487 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6487
  have eq6532 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq6529 X0
       have j1 := eq383 y X0
       grind)
    | (have r₁ := eq6529 X0
       have r₂ := eq383 y x
       grind)
    | exact resolve eq6529 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq6529
  have eq6551 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq6532 (σ X0)
       grind)
    | exact superpose eq6532 eq15
    | exact resolve eq15 eq6532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6532
  have eq6714 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6551 x
       grind)
    | exact superpose eq6551 eq16
    | exact resolve eq16 eq6551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6551
  have eq6869 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6714
       have i₂ := eq906 x y
       grind)
    | exact superpose eq906 eq6714
    | (have j1 := eq906 x y
       grind)
    | (have r₁ := eq6714
       have r₂ := eq906 x y
       grind)
    | exact resolve eq6714 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq6870 : y = (M.op x y) := by grind
  clear eq6869
  have eq6874 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3530
       have i₂ := eq6870
       grind)
    | exact superpose eq6870 eq3530
    | exact resolve eq3530 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530 eq6870
  have eq6896 : y = (M.op y y) := by grind
  clear eq6874
  have eq6899 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq6896
       grind)
    | exact superpose eq6896 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq6896
       grind)
    | exact resolve eq12 eq6896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6896
  have eq6948 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq6899 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6899
  have eq6992 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq6714
       have i₂ := eq6948 x
       grind)
    | exact superpose eq6948 eq6714
    | exact resolve eq6714 eq6948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714 eq6948
  have eq6998 : False := by grind
  exact eq6998

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxy_x_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 (M.op x y) X0
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (τ (σ y)) = (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (M.op (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq102
    | exact resolve eq102 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq105 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq103
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq103
    | exact resolve eq103 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq125 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq128
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq128
    | exact resolve eq128 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq152 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq125
    | exact resolve eq125 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq164 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq149
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq149
    | exact resolve eq149 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq167 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq152
    | exact resolve eq152 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq201 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq243 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq243
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq243
    | exact resolve eq243 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq248 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq244
       have i₂ := eq83 sF6
       grind)
    | exact superpose eq83 eq244
    | exact resolve eq244 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq285 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq105 eq9
    | exact resolve eq9 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : (k (τ (σ y)) (τ (σ y))) = (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq285
       have i₂ := eq83 (k sF2 sF2)
       grind)
    | exact superpose eq83 eq285
    | exact resolve eq285 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq294 : ∀ X0 : G, (M.op X0 (M.op (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (M.op X0 (k (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : (σ y) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq83 sF6
       grind)
    | exact superpose eq83 eq65
    | exact resolve eq65 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | (have r₁ := eq295 X0 X0
       have r₂ := eq83 X0
       grind)
    | exact resolve eq295 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq301 : ∀ X0 : G, (M.op X0 (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq294 X0
       have i₂ := eq83 (k X0 X0)
       grind)
    | exact superpose eq83 eq294
    | exact resolve eq294 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq425 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (M.op X0 X1)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq83
    | exact resolve eq83 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq439
    | exact resolve eq439 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq446 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq83 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq83 eq438
    | exact resolve eq438 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq459 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (k X0 X1) (k X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq83 (k X0 X1)
       grind)
    | exact superpose eq83 eq425
    | (have j0 := eq425 X0 X1
       grind)
    | exact resolve eq425 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq462 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq446 X0 X1
       have i₂ := eq445 (M.op X0 X1) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq445 eq446
    | exact resolve eq446 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq473 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op X1 (k X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq459
    | (have j0 := eq459 X0 X1
       grind)
    | exact resolve eq459 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq476 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 (k X1 X1))) (M.op (M.op X0 X1) (M.op X0 (k X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq462 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq462
    | exact resolve eq462 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq485 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X1 X0)) = (k (k X0 X1) (k X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq473 X0 X1
       have i₂ := eq445 X1 X0
       grind)
    | exact superpose eq445 eq473
    | (have j0 := eq473 X0 X1
       grind)
    | exact resolve eq473 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq487 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 X1
       have i₂ := eq445 X0 X1
       grind)
    | exact superpose eq445 eq476
    | exact resolve eq476 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq491 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ (k (M.op X1 X0) (M.op X1 X0)) = (k (k X0 X1) (k X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq485
    | (have j0 := eq485 X0 X1
       grind)
    | exact resolve eq485 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq492 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1
       have i₂ := eq445 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq445 eq487
    | exact resolve eq487 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq493 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X1 X0)) = (k (k X0 X1) (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq491 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq491
    | (have j0 := eq491 X0 X1
       grind)
    | exact resolve eq491 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq494 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 X1
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq492
    | exact resolve eq492 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq577 : (σ y) = (M.op (σ x) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq164 eq65
    | exact resolve eq65 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq578 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq164 eq33
    | exact resolve eq33 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq164
  have eq581 : (σ y) = (M.op (σ x) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq577
       have i₂ := eq83 (k sF5 sF5)
       grind)
    | exact superpose eq83 eq577
    | exact resolve eq577 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq583 : (σ y) = (k (M.op (σ x) (k (σ y) (σ y))) (M.op (σ x) (k (σ y) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq581
       have i₂ := eq445 sF4 (k sF5 sF5)
       grind)
    | exact superpose eq445 eq581
    | exact resolve eq581 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq584 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq583
       have i₂ := eq445 sF4 sF5
       grind)
    | exact superpose eq445 eq583
    | exact resolve eq583 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq585 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq584
    | exact resolve eq584 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq587 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq286 eq62
    | exact resolve eq62 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq587
       have i₂ := eq83 (k (k sF2 sF2) (k sF2 sF2))
       grind)
    | exact superpose eq83 eq587
    | exact resolve eq587 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq599 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq594
       have i₂ := eq445 (τ sF4) (k (k sF2 sF2) (k sF2 sF2))
       grind)
    | exact superpose eq445 eq594
    | exact resolve eq594 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq602 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (k (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) (M.op (τ (σ x)) (k (M.op x y) (M.op x y)))) (k (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) (M.op (τ (σ x)) (k (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq599
       have i₂ := eq445 (τ sF4) (k sF2 sF2)
       grind)
    | exact superpose eq445 eq599
    | exact resolve eq599 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq604 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (k (k (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y)))) (k (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))))) := by
    first
    | (have i₁ := eq602
       have i₂ := eq445 (τ sF4) sF2
       grind)
    | exact superpose eq445 eq602
    | exact resolve eq602 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq606 : (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | (have i₁ := eq604
       have i₂ := eq494 (τ sF4) sF2
       grind)
    | exact superpose eq494 eq604
    | exact resolve eq604 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq608 : (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | (have i₁ := eq606
       have i₂ := eq83 (k (τ sF5) (τ sF5))
       grind)
    | exact superpose eq83 eq606
    | exact resolve eq606 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq615 : (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) = (M.op (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq608 eq62
    | exact resolve eq62 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq622 : (M.op (τ (σ x)) (M.op (M.op x y) (M.op x y))) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | (have i₁ := eq615
       have i₂ := eq83 (k (k (τ sF5) (τ sF5)) (k (τ sF5) (τ sF5)))
       grind)
    | exact superpose eq83 eq615
    | exact resolve eq615 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq627 : (τ (σ y)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    first
    | exact superpose eq63 eq622
    | exact resolve eq622 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq622
  have eq642 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq167 eq15
    | exact resolve eq15 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq642
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq642
    | exact resolve eq642 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq651 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq647
    | exact resolve eq647 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq654 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq651 eq15
    | exact resolve eq15 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq655 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq654
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq654
    | exact resolve eq654 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq656 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq655
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq655
    | exact resolve eq655 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq657 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq656
    | exact resolve eq656 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq1448 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op X0 (τ (σ x))) (M.op X0 (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq657 eq445
    | exact resolve eq445 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq1466 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq301 X0
       have i₂ := eq445 X0 (k X0 X0)
       grind)
    | exact superpose eq445 eq301
    | exact resolve eq301 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1467 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq297 X0 X1
       have i₂ := eq445 X0 (M.op X0 X1)
       grind)
    | exact superpose eq445 eq297
    | exact resolve eq297 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1483 : (σ y) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq299
       have i₂ := eq445 sF4 sF6
       grind)
    | exact superpose eq445 eq299
    | exact resolve eq299 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1497 : ∀ X0 : G, (k (k (M.op X0 X0) (M.op X0 X0)) (k (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1466 x
       have i₂ := eq445 x x
       grind)
    | exact superpose eq445 eq1466
    | exact resolve eq1466 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1512 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1497 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq1497
    | exact resolve eq1497 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1897 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq300
    | (have j0 := eq300 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq300 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq1904 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq300
    | (have j0 := eq300 (σ y) (σ x)
       grind)
    | exact resolve eq300 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq2059 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq585 eq301
    | exact resolve eq301 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq2529 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq167 eq1897
    | (have r₁ := eq1897
       have r₂ := eq167
       grind)
    | exact resolve eq1897 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq1897
  have eq2530 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq2529
  have eq2531 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq2530
  have eq2591 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq2531 eq15
    | exact resolve eq15 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531
  have eq2601 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2591
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2591
    | exact resolve eq2591 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591
  have eq2603 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2601
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq2601
    | exact resolve eq2601 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2601
  have eq2659 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2603 eq15
    | exact resolve eq15 eq2603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2665 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2659
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2659
    | exact resolve eq2659 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659
  have eq2666 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2665
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq2665
    | exact resolve eq2665 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq2667 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq2666
    | exact resolve eq2666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2666
  have eq3083 : ∀ X0 X1 : G, (M.op X1 X0) = (k (k (k (k X0 X1) (k X0 X1)) (k (k X0 X1) (k X0 X1))) (k (k (k X0 X1) (k X0 X1)) (k (k X0 X1) (k X0 X1)))) ∨ (M.op X1 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq494 X1 X0
       have i₂ := eq493 X0 X1
       grind)
    | exact superpose eq493 eq494
    | (have j1 := eq493 X0 X1
       grind)
    | exact resolve eq494 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq3120 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ (M.op X1 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3083 X0 X1
       have i₂ := eq1512 (k X0 X1)
       grind)
    | exact superpose eq1512 eq3083
    | (have j0 := eq3083 X0 X1
       grind)
    | exact resolve eq3083 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083
  have eq8417 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq494 X0 (M.op X0 X1)
       have i₂ := eq1467 X0 X1
       grind)
    | exact superpose eq1467 eq494
    | exact resolve eq494 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq8444 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X1 (M.op X1 X0))) (τ (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))
       have i₂ := eq1467 X1 X0
       grind)
    | exact superpose eq1467 eq201
    | exact resolve eq201 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8989 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1448 eq297
    | exact resolve eq297 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq1448
  have eq9046 : (τ (σ x)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq8989 x
       have i₂ := eq8417 sF2 x
       grind)
    | exact superpose eq8417 eq8989
    | exact resolve eq8989 eq8417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8417 eq8989
  have eq9056 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2059 eq33
    | exact resolve eq33 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq9083 : (k (τ (σ y)) (τ (σ y))) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq9046 eq286
    | exact resolve eq286 eq9046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq9046
  have eq9146 : (k (τ (σ y)) (τ (σ y))) = (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9083
       have i₂ := eq83 (k (k sF2 sF2) (k sF2 sF2))
       grind)
    | exact superpose eq83 eq9083
    | exact resolve eq9083 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9083
  have eq9159 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9146
       have i₂ := eq1512 sF2
       grind)
    | exact superpose eq1512 eq9146
    | exact resolve eq9146 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9146
  have eq9195 : (τ (σ x)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2667 eq1512
    | exact resolve eq1512 eq2667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq9336 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq9159 eq15
    | exact resolve eq15 eq9159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9159
  have eq9365 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9336
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq9336
    | exact resolve eq9336 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9336
  have eq9369 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq9365
    | exact resolve eq9365 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9365
  have eq9370 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq9369
  have eq9371 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq9370 eq36
    | exact resolve eq36 eq9370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9396 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq9370
  have eq9410 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9371
       have i₂ := eq201 sF5 sF5
       grind)
    | exact superpose eq201 eq9371
    | exact resolve eq9371 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9371
  have eq9458 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq9410 eq1512
    | exact resolve eq1512 eq9410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9410
  have eq9596 : (σ y) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq9458 eq35
    | exact resolve eq35 eq9458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9458
  have eq9623 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9596
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq9596
    | exact resolve eq9596 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9596
  have eq9631 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9623
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq9623
    | exact resolve eq9623 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9623
  have eq9638 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq9631
    | exact resolve eq9631 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9631
  have eq9667 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9638 eq301
    | exact resolve eq301 eq9638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9638
  have eq9736 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9667 eq36
    | exact resolve eq36 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq9737 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (k (σ y) (σ x)) (σ X0))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq9667 eq51
    | exact resolve eq51 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq9741 : (k (M.op x y) (M.op x y)) = (τ (k (k (σ y) (σ x)) (k (σ y) (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9667 eq72
    | exact resolve eq72 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq9752 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9667 eq9056
    | (have r₁ := eq9056
       have r₂ := eq9667
       grind)
    | exact resolve eq9056 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9056 eq9667
  have eq9753 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq9752
  have eq9758 : (k (M.op x y) (M.op x y)) = (k (τ (k (σ y) (σ x))) (τ (k (σ y) (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq9741
       have i₂ := eq201 (k sF5 sF4) (k sF5 sF4)
       grind)
    | exact superpose eq201 eq9741
    | exact resolve eq9741 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9741
  have eq9762 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (k (σ y) (σ x))) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9737 x
       have i₂ := eq47 (k sF5 sF4) x
       grind)
    | exact superpose eq47 eq9737
    | exact resolve eq9737 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq9737
  have eq9763 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq9736
       have i₂ := eq201 sF4 sF5
       grind)
    | exact superpose eq201 eq9736
    | exact resolve eq9736 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9736
  have eq9766 : (k (M.op x y) (M.op x y)) = (k (k (τ (σ y)) (τ (σ x))) (k (τ (σ y)) (τ (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq9758
       have i₂ := eq201 sF4 sF5
       grind)
    | exact superpose eq201 eq9758
    | exact resolve eq9758 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9758
  have eq9770 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (τ (σ y)) (τ (σ x))) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9762 X0
       have i₂ := eq201 sF4 sF5
       grind)
    | exact superpose eq201 eq9762
    | exact resolve eq9762 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9762
  have eq10268 : (σ y) = (M.op (σ x) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9753 eq299
    | exact resolve eq299 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9753
  have eq10280 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq10268
       have i₂ := eq301 sF4
       grind)
    | exact superpose eq301 eq10268
    | exact resolve eq10268 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10268
  have eq10324 : (σ y) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq10280 eq1467
    | exact resolve eq1467 eq10280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10280
  have eq10328 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq10324
       have i₂ := eq83 sF6
       grind)
    | exact superpose eq83 eq10324
    | exact resolve eq10324 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10324
  have eq11405 : ∀ X0 X1 : G, (τ X1) = (k (τ (M.op X0 (k X0 X0))) (τ (M.op X0 (k X0 X0)))) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8444 X0 X1
       have i₂ := eq3120 X0 X1
       grind)
    | exact superpose eq3120 eq8444
    | (have j1 := eq3120 X1 X0
       grind)
    | exact resolve eq8444 eq3120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120 eq8444
  have eq11485 : ∀ X0 X1 : G, (τ X1) = (k (τ (k (M.op X0 X0) (M.op X0 X0))) (τ (k (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11405 X1 X1
       have i₂ := eq445 X1 X1
       grind)
    | exact superpose eq445 eq11405
    | (have j0 := eq11405 X0 X1
       grind)
    | exact resolve eq11405 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11405
  have eq11529 : ∀ X0 X1 : G, (τ X1) = (k (k (τ (M.op X0 X0)) (τ (M.op X0 X0))) (k (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11485 X0 X1
       have i₂ := eq201 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq201 eq11485
    | (have j0 := eq11485 X0 X1
       grind)
    | exact resolve eq11485 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11485
  have eq11550 : ∀ X0 X1 : G, (τ X1) = (k (k (τ (k X0 X0)) (τ (k X0 X0))) (k (τ (k X0 X0)) (τ (k X0 X0)))) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11529 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq11529
    | (have j0 := eq11529 X0 X1
       grind)
    | exact resolve eq11529 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11529
  have eq11563 : ∀ X0 X1 : G, (τ X1) = (k (k (k (τ X0) (τ X0)) (k (τ X0) (τ X0))) (k (k (τ X0) (τ X0)) (k (τ X0) (τ X0)))) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11550 X0 X1
       have i₂ := eq201 X0 X0
       grind)
    | exact superpose eq201 eq11550
    | (have j0 := eq11550 X0 X1
       grind)
    | exact resolve eq11550 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11550
  have eq11570 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (τ X0) = (τ X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11563 X0 X1
       have i₂ := eq1512 (τ X0)
       grind)
    | exact superpose eq1512 eq11563
    | (have j0 := eq11563 X0 X1
       grind)
    | exact resolve eq11563 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11563
  have eq15143 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq10328 eq1512
    | exact resolve eq1512 eq10328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15622 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15143 eq33
    | exact resolve eq33 eq15143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15634 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15143 eq1904
    | (have r₁ := eq1904
       have r₂ := eq15143
       grind)
    | exact resolve eq1904 eq15143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15143
  have eq15658 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq15634
  have eq21345 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq11570
    | (have j0 := eq11570 (σ x) (σ y)
       grind)
    | exact resolve eq11570 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11570
  have eq21994 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21345 eq33
    | exact resolve eq33 eq21345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21345
  have eq207100 : (σ x) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq9195 eq35
    | exact resolve eq35 eq9195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9195
  have eq207134 : (σ x) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq207100
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq207100
    | exact resolve eq207100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207100
  have eq207141 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq207134
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq207134
    | exact resolve eq207134 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207134
  have eq207147 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq207141
    | exact resolve eq207141 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207141
  have eq236668 : (σ y) = (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15658 eq1512
    | exact resolve eq1512 eq15658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15658
  have eq236724 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq236668
       have i₂ := eq1512 sF4
       grind)
    | exact superpose eq1512 eq236668
    | exact resolve eq236668 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236668
  have eq236725 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq236724
  have eq236819 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq236725 eq201
    | exact resolve eq201 eq236725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq236725
  have eq237196 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq236819 eq9766
    | exact resolve eq9766 eq236819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9766
  have eq237200 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq236819 eq9770
    | exact resolve eq9770 eq236819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9770
  have eq237232 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq237200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237200
  have eq237236 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq237196
  have eq237594 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq237232 eq9763
    | exact resolve eq9763 eq237232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9763
  have eq237623 : (τ (σ y)) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq237232 eq236819
    | exact resolve eq236819 eq237232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236819 eq237232
  have eq237829 : (τ (σ y)) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq237623
  have eq237847 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq237594
  have eq237889 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq237847 eq15
    | exact resolve eq15 eq237847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237847
  have eq237910 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq237889
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq237889
    | exact resolve eq237889 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237889
  have eq237913 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq237910
    | exact resolve eq237910 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237910
  have eq255168 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq237236 eq105
    | exact resolve eq105 eq237236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq255249 : (σ (k (M.op x y) (M.op x y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq237236 eq15
    | exact resolve eq15 eq237236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237236
  have eq255283 : (σ (k (M.op x y) (M.op x y))) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq255249
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq255249
    | exact resolve eq255249 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255249
  have eq255288 : (k (M.op x y) (M.op x y)) = (k (M.op (τ (σ x)) (M.op x y)) (M.op (τ (σ x)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq255168
       have i₂ := eq445 (τ sF4) sF2
       grind)
    | exact superpose eq445 eq255168
    | exact resolve eq255168 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq255168
  have eq255292 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq255283
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq255283
    | exact resolve eq255283 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255283
  have eq255294 : (k (M.op x y) (M.op x y)) = (k (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq608 eq255288
    | exact resolve eq255288 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq255288
  have eq255295 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq255292
    | exact resolve eq255292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255292
  have eq255296 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq627 eq255294
    | exact resolve eq255294 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq255294
  have eq255616 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq255296 eq237829
    | exact resolve eq237829 eq255296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237829
  have eq255640 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq255296 eq35
    | exact resolve eq35 eq255296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255296
  have eq255678 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq255616
  have eq255724 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq255640
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq255640
    | exact resolve eq255640 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255640
  have eq255747 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq255724
    | exact resolve eq255724 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255724
  have eq256196 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq255295 eq255747
    | exact resolve eq255747 eq255295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255747
  have eq256290 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq256196
  have eq256362 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq256290 eq248
    | exact resolve eq248 eq256290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq256290
  have eq256717 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32 eq256362
    | exact resolve eq256362 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256362
  have eq256791 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq256717 eq10328
    | exact resolve eq10328 eq256717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10328
  have eq256873 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq256791
  have eq257020 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq256873 eq256717
    | exact resolve eq256717 eq256873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256717 eq256873
  have eq257068 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq257020
  have eq257170 : (σ y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq257068 eq1467
    | exact resolve eq1467 eq257068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257068
  have eq257220 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq257170
       have i₂ := eq83 sF3
       grind)
    | exact superpose eq83 eq257170
    | exact resolve eq257170 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257170
  have eq261023 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq257220 eq1512
    | exact resolve eq1512 eq257220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257220
  have eq261206 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq261023 eq21994
    | (have r₁ := eq21994
       have r₂ := eq261023
       grind)
    | exact resolve eq21994 eq261023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21994 eq261023
  have eq261958 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq261206
  have eq262803 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq255678 eq15
    | exact resolve eq15 eq255678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255678
  have eq262817 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq262803
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq262803
    | exact resolve eq262803 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262803
  have eq262819 : (k (σ (M.op x y)) (σ x)) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq262817
    | exact resolve eq262817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262817
  have eq262820 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq262819
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq262819
    | exact resolve eq262819 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262819
  have eq262821 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq262820
    | exact resolve eq262820 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq262820
  have eq262967 : (k (σ (M.op x y)) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq262821 eq255295
    | exact resolve eq255295 eq262821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255295 eq262821
  have eq263063 : (k (σ (M.op x y)) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq262967
  have eq263146 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq263063 eq237913
    | exact resolve eq237913 eq263063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237913 eq263063
  have eq263186 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq263146
  have eq263205 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq263186
       have r₂ := eq15622
       grind)
    | exact resolve eq263186 eq15622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15622 eq263186
  have eq263261 : (σ y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq263205 eq1467
    | exact resolve eq1467 eq263205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq263205
  have eq263323 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq263261
       have i₂ := eq83 sF3
       grind)
    | exact superpose eq83 eq263261
    | exact resolve eq263261 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq263261
  have eq263432 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq263323 eq1512
    | exact resolve eq1512 eq263323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263323
  have eq263551 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq263432 eq578
    | (have r₁ := eq578
       have r₂ := eq263432
       grind)
    | exact resolve eq578 eq263432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq264141 : (σ x) = (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq263432 eq207147
    | exact resolve eq207147 eq263432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207147
  have eq264403 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq263551
  have eq264427 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq264141
       have i₂ := eq1512 sF5
       grind)
    | exact superpose eq1512 eq264141
    | exact resolve eq264141 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512 eq264141
  have eq264428 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq264427
  have eq266076 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq264403 eq1904
    | exact resolve eq1904 eq264403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq266160 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq264403
  have eq266227 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq266076
       have r₂ := eq266160
       grind)
    | exact resolve eq266076 eq266160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266076 eq266160
  have eq266231 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq266227
       have r₂ := eq264428
       grind)
    | exact resolve eq266227 eq264428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264428 eq266227
  have eq266408 : (σ y) = (M.op (σ x) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq266231 eq299
    | exact resolve eq299 eq266231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq266231
  have eq266580 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq266408
       have i₂ := eq301 sF4
       grind)
    | exact superpose eq301 eq266408
    | exact resolve eq266408 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq266408
  have eq266581 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq266580
  have eq332184 : (σ y) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq261958
  have eq332233 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq332184
       have r₂ := eq266581
       grind)
    | exact resolve eq332184 eq266581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266581 eq332184
  have eq332653 : (σ y) = (σ (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq332233 eq35
    | exact resolve eq35 eq332233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332233
  have eq332808 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq332653
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq332653
    | exact resolve eq332653 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq332653
  have eq332809 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq332808
  have eq332855 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq332809 eq33
    | exact resolve eq33 eq332809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332868 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq332809 eq1483
    | exact resolve eq1483 eq332809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq333097 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32 eq332868
    | exact resolve eq332868 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq332868
  have eq333126 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq263432 eq332855
    | exact resolve eq332855 eq263432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263432 eq332855
  have eq333133 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq333126
  have eq333676 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq332809 eq333097
    | exact resolve eq333097 eq332809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332809 eq333097
  have eq333819 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq333676
  have eq333846 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq333819
       have r₂ := eq333133
       grind)
    | exact resolve eq333819 eq333133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333133 eq333819
  have eq333857 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq333846 eq580
    | exact resolve eq580 eq333846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq333929 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq333846 eq9396
    | exact resolve eq9396 eq333846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9396 eq333846
  have eq334733 : (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq333929
  have eq334787 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq333857
  have eq334788 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq334787
  have eq337785 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq334788 eq33
    | exact resolve eq33 eq334788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq334788
  have eq337928 : False := by grind
  exact eq337928

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_y_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
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
  have eq50 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq10
    | exact resolve eq10 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq43
    | exact resolve eq43 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq68 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq66
    | exact resolve eq66 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
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
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq94 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq64 sF3
       grind)
    | exact superpose eq64 eq92
    | exact resolve eq92 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq64 y
       grind)
    | exact superpose eq64 eq94
    | exact resolve eq94 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 (σ X0) (σ X1)
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
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
  have eq143 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq64 sF1
       grind)
    | exact superpose eq64 eq140
    | exact resolve eq140 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq143
       have i₂ := eq64 sF0
       grind)
    | exact superpose eq64 eq143
    | exact resolve eq143 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq143
  have eq441 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq69 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq69
    | exact resolve eq69 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq52 (M.op X1 X1) X0
       grind)
    | exact superpose eq52 eq550
    | exact resolve eq550 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq557 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq546
       have i₂ := eq52 sF4 sF4
       grind)
    | exact superpose eq52 eq546
    | exact resolve eq546 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq559 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq543
       have i₂ := eq52 sF0 sF0
       grind)
    | exact superpose eq52 eq543
    | exact resolve eq543 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq562 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq52 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq52 eq539
    | exact resolve eq539 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq563 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq52 X1 X1
       grind)
    | exact superpose eq52 eq554
    | exact resolve eq554 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq568 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq562
    | exact resolve eq562 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq621 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq98
  have eq734 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq621 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq621
    | (have j0 := eq621 x X0
       grind)
    | exact resolve eq621 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq812 : (τ (σ (M.op x y))) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq112 eq58
    | exact resolve eq58 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq112 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq813
    | exact resolve eq813 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq815 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq30 eq812
    | exact resolve eq812 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq817 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq814
       have r₂ := eq27
       grind)
    | exact resolve eq814 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq819 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq817
    | exact resolve eq817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq821 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq819 eq54
    | exact resolve eq54 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq829 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq819 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq557 eq52
    | exact resolve eq52 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq917 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq913
       have i₂ := eq52 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq52 eq913
    | exact resolve eq913 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq919 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq917
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq917
    | exact resolve eq917 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq920 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq919
       have i₂ := eq52 sF3 sF3
       grind)
    | exact superpose eq52 eq919
    | exact resolve eq919 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq931 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq559 eq52
    | exact resolve eq52 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq931
       have i₂ := eq52 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq52 eq931
    | exact resolve eq931 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq936 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq935
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq935
    | exact resolve eq935 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq937 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq936
       have i₂ := eq52 y y
       grind)
    | exact superpose eq52 eq936
    | exact resolve eq936 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq2472 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))))) := by
    first
    | exact superpose eq51 eq563
    | exact resolve eq563 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2550 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2472
       have i₂ := eq548 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq548 eq2472
    | exact resolve eq2472 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472
  have eq2683 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X0 (σ y)) (M.op X0 (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq819 eq568
    | exact resolve eq568 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq2712 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq568 X0 X1
       grind)
    | exact superpose eq568 eq52
    | exact resolve eq52 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq2716 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2712 X0 X1
       have i₂ := eq52 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq52 eq2712
    | exact resolve eq2712 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712
  have eq2777 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2716 X0 X1
       have i₂ := eq52 (M.op X0 X0) X1
       grind)
    | exact superpose eq52 eq2716
    | exact resolve eq2716 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716
  have eq2808 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2777 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq2777
    | exact resolve eq2777 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq2819 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2808 X0 X1
       have i₂ := eq563 X1 X0
       grind)
    | exact superpose eq563 eq2808
    | exact resolve eq2808 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq2808
  have eq3989 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq2683
    | (have j0 := eq2683 (σ x)
       grind)
    | exact resolve eq2683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq4104 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq734 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq734
    | (have j0 := eq734 y
       grind)
    | exact resolve eq734 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq4120 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4104
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4104
    | exact resolve eq4104 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104
  have eq4136 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq4120
    | exact resolve eq4120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120
  have eq4144 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4136
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq4136
    | exact resolve eq4136 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq4151 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq4144
    | exact resolve eq4144 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq7419 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ≠ X0 ∨ (M.op (M.op X1 (M.op X0 X0)) X1) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X1 (M.op X0 X0) X1
       have i₂ := eq548 X1 X0
       grind)
    | exact superpose eq548 eq551
    | (have j0 := eq551 X1 (M.op X0 X0) X1
       grind)
    | exact resolve eq551 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq7506 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) ≠ X0 ∨ (M.op (M.op X1 (M.op X0 X0)) X1) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7419 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq7419
    | (have j0 := eq7419 X0 X1
       grind)
    | exact resolve eq7419 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7419
  have eq7628 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) ≠ X0 ∨ (M.op (M.op X1 (M.op X0 X0)) X1) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7506 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq7506
    | (have j0 := eq7506 X0 X1
       grind)
    | exact resolve eq7506 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7506
  have eq11521 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq821 eq2819
    | exact resolve eq2819 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq11637 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq559
       have i₂ := eq2819 sF0 x
       grind)
    | (have i₁ := eq559
       have i₂ := eq2819 sF0 sF0
       grind)
    | exact superpose eq2819 eq559
    | exact resolve eq559 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq21961 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq11521 eq3989
    | exact resolve eq3989 eq11521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989 eq11521
  have eq21983 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq21961 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21961
  have eq52243 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq441
       have i₂ := eq52 y y
       grind)
    | exact superpose eq52 eq441
    | exact resolve eq441 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq52244 : (σ (M.op x (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq52243
       have i₂ := eq937
       grind)
    | exact superpose eq937 eq52243
    | exact resolve eq52243 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq52243
  have eq52245 : (σ (M.op x (M.op x y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq52244
       have i₂ := eq52 sF3 sF3
       grind)
    | exact superpose eq52 eq52244
    | exact resolve eq52244 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52244
  have eq52246 : (σ (M.op x (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq920 eq52245
    | exact resolve eq52245 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq52245
  have eq661725 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) ∨ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21983 eq7628
    | (have j0 := eq7628 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq7628 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq21983 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq7628 eq21983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21983
  have eq661745 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) ∨ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq661725
  have eq661767 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq51 eq661745
    | exact resolve eq661745 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661745
  have eq661845 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq51 eq661767
    | exact resolve eq661767 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq661767
  have eq662083 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq661845 eq829
    | (have j0 := eq829 (σ x)
       grind)
    | (have r₁ := eq829 (σ x)
       have r₂ := eq661845
       grind)
    | exact resolve eq829 eq661845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq661845
  have eq662110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq662083
  have eq662111 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq662110
  have eq662113 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq662111
    | exact resolve eq662111 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662111
  have eq662114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq112 eq662113
    | exact resolve eq662113 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq662113 eq112
    | exact resolve eq112 eq662113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq662113
  have eq662161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq662119
  have eq662162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq662114
  have eq662168 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq662161
       have r₂ := eq27
       grind)
    | exact resolve eq662161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662161
  have eq662169 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq662162
       have r₂ := eq27
       grind)
    | exact resolve eq662162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662162
  have eq662171 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq53
       have i₂ := eq662169
       grind)
    | exact superpose eq662169 eq53
    | exact resolve eq53 eq662169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662172 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq662169
       grind)
    | exact superpose eq662169 eq96
    | exact resolve eq96 eq662169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662169
  have eq662348 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq662172
    | exact resolve eq662172 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662172
  have eq665175 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq662348 eq52
    | exact resolve eq52 eq662348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662348
  have eq667647 : (τ (σ y)) = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq662168 eq58
    | exact resolve eq58 eq662168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq662168
  have eq667699 : (M.op x y) = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq29 eq667647
    | exact resolve eq667647 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq667647
  have eq667707 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq662171 eq145
    | exact resolve eq145 eq662171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662171
  have eq667870 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52246 eq667707
    | exact resolve eq667707 eq52246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52246 eq667707
  have eq690943 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq667870 eq14
    | exact resolve eq14 eq667870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667870
  have eq690983 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq690943
       have i₂ := eq52 sF1 sF1
       grind)
    | exact superpose eq52 eq690943
    | exact resolve eq690943 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq690943
  have eq792364 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq690983
       have i₂ := eq2819 sF1 x
       grind)
    | (have i₁ := eq690983
       have i₂ := eq2819 sF1 sF1
       grind)
    | exact superpose eq2819 eq690983
    | exact resolve eq690983 eq2819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819 eq690983
  have eq807814 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq665175 eq792364
    | exact resolve eq792364 eq665175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665175 eq792364
  have eq807875 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq807814
  have eq1595094 : (M.op x y) ≠ (M.op y y) ∨ (M.op y y) = (M.op (M.op x (M.op (M.op x y) (M.op x y))) x) ∨ (M.op x (M.op (M.op x y) (M.op x y))) = (k x (M.op x (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq11637 eq7628
    | (have j0 := eq7628 (M.op x y) x
       grind)
    | exact resolve eq7628 eq11637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7628 eq11637
  have eq1595180 : (M.op y y) = (M.op y x) ∨ (M.op x y) ≠ (M.op y y) ∨ (M.op x (M.op (M.op x y) (M.op x y))) = (k x (M.op x (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq50 eq1595094
    | exact resolve eq1595094 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595094
  have eq1595248 : y = (k x y) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) ≠ (M.op y y) := by
    first
    | exact superpose eq50 eq1595180
    | exact resolve eq1595180 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595180
  have eq1595281 : (M.op y y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have r₁ := eq1595248
       have r₂ := eq667699
       grind)
    | exact resolve eq1595248 eq667699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667699 eq1595248
  have eq1595595 : y = (M.op y (M.op (M.op y x) (M.op y x))) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq1595281
       grind)
    | exact superpose eq1595281 eq14
    | exact resolve eq14 eq1595281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595281
  have eq1595661 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq1595595
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1595595
    | exact resolve eq1595595 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595595
  have eq1595907 : (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1595661
       have i₂ := eq815
       grind)
    | exact superpose eq815 eq1595661
    | exact resolve eq1595661 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq1595910 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq1595661
       grind)
    | exact superpose eq1595661 eq44
    | exact resolve eq44 eq1595661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1595661
  have eq1596109 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1595910
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1595910
    | exact resolve eq1595910 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595910
  have eq1596698 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4151 eq1596109
    | exact resolve eq1596109 eq4151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4151 eq1596109
  have eq1599640 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq1595907
       grind)
    | exact superpose eq1595907 eq96
    | exact resolve eq96 eq1595907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1595907
  have eq1599963 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1599640
    | exact resolve eq1599640 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599640
  have eq1601113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1599963 eq1596698
    | exact resolve eq1596698 eq1599963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1601304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1601113
  have eq1601324 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1601304
       have r₂ := eq27
       grind)
    | exact resolve eq1601304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601304
  have eq1601347 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1601324 eq27
    | exact resolve eq27 eq1601324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1601416 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1601324 eq2550
    | exact resolve eq2550 eq1601324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq1602807 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1601416
    | exact resolve eq1601416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601416
  have eq1604072 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1601324 eq1602807
    | exact resolve eq1602807 eq1601324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601324 eq1602807
  have eq1604474 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1604072
  have eq1605264 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1604474 eq1599963
    | exact resolve eq1599963 eq1604474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599963 eq1604474
  have eq1605455 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1605264
  have eq1605498 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1605455
       have r₂ := eq1601347
       grind)
    | exact resolve eq1605455 eq1601347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601347 eq1605455
  have eq1606202 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1605498 eq20
    | exact resolve eq20 eq1605498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1606204 : y = (M.op x (M.op y y)) ∨ x = y := by
    first
    | exact superpose eq1605498 eq50
    | exact resolve eq50 eq1605498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1605498
  have eq1607465 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1606204
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq1606204
    | exact resolve eq1606204 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1606204
  have eq1607467 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1606202
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1606202
    | exact resolve eq1606202 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606202
  have eq1608825 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1607467 eq1596698
    | exact resolve eq1596698 eq1607467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596698
  have eq1608839 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq1608825
  have eq1608842 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq1608839
       have r₂ := eq27
       grind)
    | exact resolve eq1608839 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608839
  have eq1609169 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1607465 eq145
    | exact resolve eq145 eq1607465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq1607465
  have eq1609524 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1609169
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1609169
    | exact resolve eq1609169 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609169
  have eq1611519 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1609524 eq1608842
    | exact resolve eq1608842 eq1609524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608842 eq1609524
  have eq1611665 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1611519
  have eq1611692 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1611665 eq27
    | exact resolve eq27 eq1611665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611665
  have eq1614151 : x = y := by
    first
    | (have r₁ := eq1611692
       have r₂ := eq1607467
       grind)
    | exact resolve eq1611692 eq1607467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607467 eq1611692
  have eq1614896 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1614151
       grind)
    | exact superpose eq1614151 eq18
    | exact resolve eq18 eq1614151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1614897 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1614151
       grind)
    | exact superpose eq1614151 eq24
    | exact resolve eq24 eq1614151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1614151
  have eq1616089 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1614897
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1614897
    | exact resolve eq1614897 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614897
  have eq1616171 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1616089 eq26
    | exact resolve eq26 eq1616089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1617433 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1616089 eq807875
    | exact resolve eq807875 eq1616089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807875 eq1616089
  have eq1617728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1617433
       have i₂ := eq548 sF2 sF1
       grind)
    | exact superpose eq548 eq1617433
    | exact resolve eq1617433 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq1617433
  have eq1618724 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1617728
       have r₂ := eq27
       grind)
    | exact resolve eq1617728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617728
  have eq1619038 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq1618724 eq28
    | exact resolve eq28 eq1618724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1620324 : x = (M.op x y) := by
    first
    | exact superpose eq30 eq1619038
    | exact resolve eq1619038 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1619038
  have eq1624089 : x = (M.op x x) := by
    first
    | exact superpose eq1620324 eq1614896
    | exact resolve eq1614896 eq1620324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614896 eq1620324
  have eq1624094 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq1624089
       grind)
    | exact superpose eq1624089 eq68
    | exact resolve eq68 eq1624089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1624089
  have eq1624332 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1618724 eq1624094
    | exact resolve eq1624094 eq1618724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624094
  have eq1624415 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1624332
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1624332
    | exact resolve eq1624332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1624332
  have eq1624488 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1618724 eq1624415
    | exact resolve eq1624415 eq1618724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624415
  have eq1624697 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1618724 eq1616171
    | exact resolve eq1616171 eq1618724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616171 eq1618724
  have eq1625284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1624488 eq1624697
    | exact resolve eq1624697 eq1624488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624488 eq1624697
  have eq1625285 : False := by grind
  exact eq1625285

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_x_pyy_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  clear eq23
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 (M.op X0 X1) X2
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq65
    | exact resolve eq65 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 X0 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq65
    | exact resolve eq65 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq65 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq65 X0 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq71 (M.op X0 X0)
       have i₂ := eq65 X0 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq71
    | exact resolve eq71 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq79
    | exact resolve eq79 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq94 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq65 X0 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq70
    | exact resolve eq70 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq94
    | exact resolve eq94 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq129 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 X1 X2
       have i₂ := eq118 X1 X0
       grind)
    | (have i₁ := eq118 X0 X1
       have i₂ := eq118 X0 X0
       grind)
    | exact superpose eq118 eq118
    | exact resolve eq118 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X1 X1 X2
       have i₂ := eq118 X1 X0
       grind)
    | (have i₁ := eq70 X0 X0 X2
       have i₂ := eq118 X0 X0
       grind)
    | exact superpose eq118 eq70
    | exact resolve eq70 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq135 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 X1
       have i₂ := eq118 X1 X0
       grind)
    | (have i₁ := eq65 X0 X0
       have i₂ := eq118 X0 X0
       grind)
    | exact superpose eq118 eq65
    | exact resolve eq65 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1
       have i₂ := eq118 X1 X0
       grind)
    | (have i₁ := eq82 X0
       have i₂ := eq118 X0 X0
       grind)
    | exact superpose eq118 eq82
    | exact resolve eq82 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq118
  have eq254 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq135 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq139 X1 X0
       grind)
    | exact superpose eq139 eq135
    | exact resolve eq135 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq419 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X1 X2 X1
       have i₂ := eq129 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq134 X1 X2 X1
       have i₂ := eq129 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq129 eq134
    | exact resolve eq134 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq607 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) X2
       have i₂ := eq254 X0 X1
       grind)
    | exact superpose eq254 eq134
    | exact resolve eq134 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq254
  have eq613 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq607 X0 X1 X2
       have i₂ := eq64 (M.op X0 X0) (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq64 eq607
    | exact resolve eq607 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq634 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq613 X0 X1 X2
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq613
    | exact resolve eq613 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq647 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1 x
       have i₂ := eq65 X0 x
       grind)
    | exact superpose eq65 eq634
    | exact resolve eq634 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq846 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X1 X2
       have i₂ := eq129 X1 X1 X0
       grind)
    | (have i₁ := eq647 X1 X2
       have i₂ := eq129 X0 X1 X1
       grind)
    | exact superpose eq129 eq647
    | exact resolve eq647 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq647
  have eq5023 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq573 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq573 X0 X1
       grind)
    | exact superpose eq573 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq573 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq573 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq573 X1 X1
       grind)
    | exact resolve eq13 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5024 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (M.op (σ X0) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq573 X0 X1
       grind)
    | (have i₁ := eq64 (σ X1) (σ X0)
       have i₂ := eq573 X0 X1
       grind)
    | exact superpose eq573 eq64
    | (have j1 := eq573 X0 X1
       grind)
    | exact resolve eq64 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq5049 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5023 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023
  have eq5050 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5049 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049
  have eq5057 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ X0) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5024 X0 X1
       have i₂ := eq64 (σ X0) (σ X0)
       grind)
    | exact superpose eq64 eq5024
    | (have j0 := eq5024 X0 X1
       grind)
    | exact resolve eq5024 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq5024
  have eq5058 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5050 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5050
    | (have j0 := eq5050 X0 X1
       grind)
    | exact resolve eq5050 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5050
  have eq39955 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq40113 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5058 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5058
  have eq40122 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq39955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39955
  have eq46493 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))) (M.op X2 (M.op X2 (M.op (σ X1) (σ X1))))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq846 X2 (M.op (σ X1) (σ X1)) (σ X0)
       have i₂ := eq5057 X0 X1
       grind)
    | (have i₁ := eq846 X0 (M.op (σ X0) (σ X0)) (σ X0)
       have i₂ := eq5057 X0 X1
       grind)
    | exact superpose eq5057 eq846
    | (have j1 := eq5057 X0 X1
       grind)
    | exact resolve eq846 eq5057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq5057
  have eq46554 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46493 X0 X1 x
       have i₂ := eq65 (σ X1) x
       grind)
    | exact superpose eq65 eq46493
    | (have j0 := eq46493 X0 X1 x
       grind)
    | exact resolve eq46493 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46493
  have eq46764 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46554 X0 X1
       have i₂ := eq65 (σ X0) (σ X0)
       grind)
    | exact superpose eq65 eq46554
    | (have j0 := eq46554 X0 X1
       grind)
    | exact resolve eq46554 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq46554
  have eq46968 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq46764 X0 X1
       have j1 := eq40113 X0 X1
       grind)
    | (have r₁ := eq46764 X0 X1
       have r₂ := eq40113 X0 X1
       grind)
    | (have r₁ := eq46764 X0 X0
       have r₂ := eq40113 X0 X0
       grind)
    | exact resolve eq46764 eq40113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40113 eq46764
  have eq47007 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq46968 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46968
  have eq47014 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47007 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47007
  have eq47393 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47014 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47014
  have eq47603 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47393 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47393
  have eq47754 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq47603 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47603
  have eq48274 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47754 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47754
  have eq48515 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq48274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48274
  have eq48694 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have j0 := eq48515 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48515
  have eq48875 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq48694 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48694
  have eq50273 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48875 (τ X0) (τ X1)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq48875
    | (have j0 := eq48875 (τ X0) (τ X1)
       grind)
    | exact resolve eq48875 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq50318 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50273 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq50273
    | (have j0 := eq50273 X0 X1
       grind)
    | exact resolve eq50273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50273
  have eq50338 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50318 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50318
    | (have j0 := eq50318 X0 X1
       grind)
    | exact resolve eq50318 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50318
  have eq50345 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50338 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq50338
    | (have j0 := eq50338 X0 X1
       grind)
    | exact resolve eq50338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50338
  have eq50350 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50345 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50345
    | (have j0 := eq50345 X0 X1
       grind)
    | exact resolve eq50345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50345
  have eq50355 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50350 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50350
    | (have j0 := eq50350 X0 X1
       grind)
    | exact resolve eq50350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50350
  have eq238924 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 (σ (M.op X0 X0))))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq40122 X0
       grind)
    | exact superpose eq40122 eq419
    | (have j1 := eq40122 X0
       grind)
    | exact resolve eq419 eq40122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq40122
  have eq239127 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq238924 X0 x
       have i₂ := eq135 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq135 eq238924
    | (have j0 := eq238924 X0 x
       grind)
    | exact resolve eq238924 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq238924
  have eq239128 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq239127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239127
  have eq239186 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq239128 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239128
  have eq239231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48875 X0 X1
       have i₂ := eq239186 X1
       grind)
    | exact superpose eq239186 eq48875
    | (have j0 := eq48875 X0 X1
       grind)
    | exact resolve eq48875 eq239186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48875
  have eq239259 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq72 (σ X0)
       have i₂ := eq239186 X0
       grind)
    | exact superpose eq239186 eq72
    | exact resolve eq72 eq239186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239186
  have eq240045 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq239231 X0 X1
       have i₂ := eq50355 X0 X1
       grind)
    | exact superpose eq50355 eq239231
    | (have j0 := eq239231 X0 X1
       have j1 := eq50355 X0 X1
       grind)
    | exact resolve eq239231 eq50355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50355 eq239231
  have eq668943 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq240045 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240045
  have eq669159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq668943 x y
       grind)
    | exact superpose eq668943 eq16
    | (have j1 := eq668943 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq668943 x y
       grind)
    | exact resolve eq16 eq668943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668943
  have eq669682 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq669159
  have eq670659 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq669682
       grind)
    | exact superpose eq669682 eq10
    | exact resolve eq10 eq669682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669682
  have eq670968 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq670659
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq670659
    | exact resolve eq670659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670659
  have eq670969 : x = (M.op y y) := by grind
  clear eq670968
  have eq671045 : x = (M.op x y) := by
    first
    | (have i₁ := eq72 y
       have i₂ := eq670969
       grind)
    | exact superpose eq670969 eq72
    | exact resolve eq72 eq670969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq671115 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq239259 y
       have i₂ := eq670969
       grind)
    | exact superpose eq670969 eq239259
    | exact resolve eq239259 eq670969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239259 eq670969
  have eq671611 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq671045
       grind)
    | exact superpose eq671045 eq16
    | exact resolve eq16 eq671045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671045
  have eq672001 : False := by grind
  exact eq672001

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq51 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
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
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq293 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq305 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq303
    | exact resolve eq303 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq307 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq299
       have i₂ := eq53 sF4 sF4
       grind)
    | exact superpose eq53 eq299
    | exact resolve eq299 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq309 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq296
       have i₂ := eq53 sF0 sF0
       grind)
    | exact superpose eq53 eq296
    | exact resolve eq296 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq311 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq53 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq293
    | exact resolve eq293 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq312 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq305
    | exact resolve eq305 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq316 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq311 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq311
    | exact resolve eq311 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq319 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301 X2 (M.op X0 X1)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq301
    | exact resolve eq301 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq301 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq301 (M.op X0 X0) X0
       grind)
    | exact superpose eq301 eq301
    | exact resolve eq301 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq301 (M.op X0 X0) X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq301
    | exact resolve eq301 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq611 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq307 eq53
    | exact resolve eq53 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq611
       have i₂ := eq53 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq53 eq611
    | exact resolve eq611 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq618 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq616
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq616
    | exact resolve eq616 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq619 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq618
       have i₂ := eq53 sF3 sF3
       grind)
    | exact superpose eq53 eq618
    | exact resolve eq618 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq624 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq619 eq301
    | exact resolve eq301 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq309 eq53
    | exact resolve eq53 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq643 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq638
       have i₂ := eq53 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq53 eq638
    | exact resolve eq638 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq645 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq643
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq643
    | exact resolve eq643 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq646 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq645
       have i₂ := eq53 y y
       grind)
    | exact superpose eq53 eq645
    | exact resolve eq645 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq669 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq301 y y
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq301
    | exact resolve eq301 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq685 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq321 (M.op X0 X0)
       have i₂ := eq301 (M.op X0 X0) X0
       grind)
    | exact superpose eq301 eq321
    | exact resolve eq321 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq685 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq685
    | exact resolve eq685 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq759 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq619 eq694
    | exact resolve eq694 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq827 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq759 eq53
    | exact resolve eq53 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq827
       have i₂ := eq53 sF3 sF3
       grind)
    | exact superpose eq53 eq827
    | exact resolve eq827 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq833 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq619 eq831
    | exact resolve eq831 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq2872 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))))) := by
    first
    | exact superpose eq52 eq316
    | exact resolve eq316 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2896 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq316 X0 X1
       grind)
    | exact superpose eq316 eq53
    | exact resolve eq53 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq2902 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2896 X0 X1
       have i₂ := eq53 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq2896
    | exact resolve eq2896 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2896
  have eq2921 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))))) := by
    first
    | (have i₁ := eq2872
       have i₂ := eq53 sF4 sF4
       grind)
    | exact superpose eq53 eq2872
    | exact resolve eq2872 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq2943 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2902 X0 X1
       have i₂ := eq53 (M.op X0 X0) X1
       grind)
    | exact superpose eq53 eq2902
    | exact resolve eq2902 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq2957 : (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq307 eq2921
    | exact resolve eq2921 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq2921
  have eq2977 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2943 X0 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq2943
    | exact resolve eq2943 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943
  have eq2984 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq619 eq2957
    | exact resolve eq2957 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2957
  have eq2999 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2977 X0 X1
       have i₂ := eq312 X1 X0
       grind)
    | exact superpose eq312 eq2977
    | exact resolve eq2977 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2977
  have eq3055 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2999 X1 X2
       have i₂ := eq2999 X1 X0
       grind)
    | (have i₁ := eq2999 X0 X1
       have i₂ := eq2999 X0 X0
       grind)
    | exact superpose eq2999 eq2999
    | exact resolve eq2999 eq2999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3058 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq619 eq2999
    | exact resolve eq2999 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3074 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq321 X1
       have i₂ := eq2999 X1 X0
       grind)
    | (have i₁ := eq321 X0
       have i₂ := eq2999 X0 X0
       grind)
    | exact superpose eq2999 eq321
    | exact resolve eq321 eq2999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq2999
  have eq3830 : (k y (M.op x (M.op x y))) = (M.op y (M.op x (M.op x y))) := by
    first
    | exact superpose eq51 eq304
    | exact resolve eq304 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3834 : (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq52 eq304
    | exact resolve eq304 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq3919 : (σ y) = (k (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq624 eq3834
    | exact resolve eq3834 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834
  have eq3922 : y = (k y (M.op x (M.op x y))) := by
    first
    | exact superpose eq669 eq3830
    | exact resolve eq3830 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3830
  have eq4424 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq624 eq3055
    | exact resolve eq3055 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11282
    | exact resolve eq11282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11282
  have eq11290 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11283
       have r₂ := eq28
       grind)
    | exact resolve eq11283 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11283
  have eq11292 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11290
    | exact resolve eq11290 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11290
  have eq11306 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11292 eq320
    | exact resolve eq320 eq11292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11292
  have eq11333 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11306
    | exact resolve eq11306 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11306
  have eq11341 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11333
  have eq11375 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11341
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11341
    | exact resolve eq11341 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11341
  have eq11520 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11375
       grind)
    | exact superpose eq11375 eq45
    | exact resolve eq45 eq11375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11375
  have eq11540 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11520
    | exact resolve eq11520 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11520
  have eq11818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11540 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq11540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11540
  have eq11819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11818
    | exact resolve eq11818 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11818
  have eq11826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11819
       have r₂ := eq28
       grind)
    | exact resolve eq11819 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11819
  have eq11828 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11826
    | exact resolve eq11826 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11826
  have eq11829 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11828
  have eq12190 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11829 eq320
    | exact resolve eq320 eq11829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq11829
  have eq12219 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12190
    | exact resolve eq12190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12190
  have eq12220 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12219
  have eq12223 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12220 eq28
    | exact resolve eq28 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12224 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12220 eq52
    | exact resolve eq52 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12227 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12220 eq624
    | exact resolve eq624 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12229 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12220 eq759
    | exact resolve eq759 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq12230 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12220 eq833
    | exact resolve eq833 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq12236 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12220 eq3919
    | exact resolve eq3919 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919
  have eq12244 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq12254 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12236
    | exact resolve eq12236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12236
  have eq12257 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12230
    | exact resolve eq12230 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12230
  have eq12258 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12229
    | exact resolve eq12229 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12229
  have eq12260 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12227
    | exact resolve eq12227 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12227
  have eq12262 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55 eq12224
    | exact resolve eq12224 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq12224
  have eq12375 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12220 eq12254
    | exact resolve eq12254 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12254
  have eq12383 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12375
  have eq12384 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12383
       have r₂ := eq12244
       grind)
    | exact resolve eq12383 eq12244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12383
  have eq12496 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12220 eq12260
    | exact resolve eq12260 eq12220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12220 eq12260
  have eq12513 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12496
  have eq12520 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12513
       have r₂ := eq12244
       grind)
    | exact resolve eq12513 eq12244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12513
  have eq12526 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12262 eq2984
    | exact resolve eq2984 eq12262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984 eq12262
  have eq12571 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12384 eq109
    | exact resolve eq109 eq12384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12384
  have eq12598 : y = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq12571
    | exact resolve eq12571 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12571
  have eq12762 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq12782 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12520 eq3074
    | exact resolve eq3074 eq12520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3074
  have eq12790 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq619 eq12782
    | exact resolve eq12782 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12782
  have eq13161 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq12598
       grind)
    | exact superpose eq12598 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq12598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12598
  have eq13162 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13161
  have eq13383 : (M.op y y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13162
  have eq13686 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12520 eq12257
    | exact resolve eq12257 eq12520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12257 eq12520
  have eq13712 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13686
  have eq13947 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13712 eq312
    | exact resolve eq312 eq13712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq13712
  have eq13964 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13947
       have i₂ := eq319 sF3 sF3 sF4
       grind)
    | exact superpose eq319 eq13947
    | exact resolve eq13947 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq13947
  have eq14030 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12258 eq14
    | exact resolve eq14 eq12258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12258
  have eq14051 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14030
       have i₂ := eq53 sF3 sF3
       grind)
    | exact superpose eq53 eq14030
    | exact resolve eq14030 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14030
  have eq14053 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq619 eq14051
    | exact resolve eq14051 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq14051
  have eq14847 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12790 eq14053
    | exact resolve eq14053 eq12790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14053
  have eq14866 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14847
  have eq14981 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14866 eq3058
    | exact resolve eq3058 eq14866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058 eq14866
  have eq15522 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12762 eq109
    | exact resolve eq109 eq12762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq12762
  have eq22656 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13964 eq15522
    | exact resolve eq15522 eq13964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13964 eq15522
  have eq22719 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22656
  have eq22742 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13383
       have i₂ := eq22719
       grind)
    | exact superpose eq22719 eq13383
    | exact resolve eq13383 eq22719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13383 eq22719
  have eq22755 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22742
  have eq33901 : (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12526 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12526
       grind)
    | exact resolve eq12 eq12526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12526
  have eq33945 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq33901
       have r₂ := eq14981
       grind)
    | exact resolve eq33901 eq14981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14981 eq33901
  have eq33962 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33945
       have i₂ := eq53 sF4 sF2
       grind)
    | exact superpose eq53 eq33945
    | exact resolve eq33945 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq33945
  have eq33972 : (σ x) = (σ y) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52 eq33962
    | exact resolve eq33962 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq33962
  have eq33973 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq33972
       have r₂ := eq12244
       grind)
    | exact resolve eq33972 eq12244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12244 eq33972
  have eq46996 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12790 eq33973
    | exact resolve eq33973 eq12790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12790 eq33973
  have eq47013 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq46996
  have eq47312 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47013 eq103
    | exact resolve eq103 eq47013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47013
  have eq47327 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq47312
  have eq47335 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq47327
       have r₂ := eq12223
       grind)
    | exact resolve eq47327 eq12223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12223 eq47327
  have eq47618 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22755
       have i₂ := eq47335
       grind)
    | exact superpose eq47335 eq22755
    | exact resolve eq22755 eq47335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22755 eq47335
  have eq47663 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq47618
  have eq48281 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47663 eq15
    | exact resolve eq15 eq47663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47663
  have eq48420 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48281
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48281
    | exact resolve eq48281 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48281
  have eq48421 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq48420
  have eq48712 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq48421 eq4424
    | exact resolve eq4424 eq48421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4424 eq48421
  have eq48716 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq48712 x
       have i₂ := eq301 x sF2
       grind)
    | exact superpose eq301 eq48712
    | exact resolve eq48712 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq48712
  have eq49014 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq48716
  have eq49086 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq49014
    | exact resolve eq49014 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49014
  have eq49353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49086 eq103
    | exact resolve eq103 eq49086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq49366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq49353
  have eq49370 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq49366
       have r₂ := eq28
       grind)
    | exact resolve eq49366 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49366
  have eq49391 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq49370
  have eq49446 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq49391
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49391
    | exact resolve eq49391 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49391
  have eq50412 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq49446
       grind)
    | exact superpose eq49446 eq45
    | exact resolve eq45 eq49446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq49446
  have eq50436 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq50412
    | exact resolve eq50412 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50412
  have eq50862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50436 eq49086
    | exact resolve eq49086 eq50436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49086 eq50436
  have eq50868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq50862
  have eq50872 : y = (M.op x y) := by
    first
    | (have r₁ := eq50868
       have r₂ := eq28
       grind)
    | exact resolve eq50868 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50868
  have eq51140 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq50872 eq21
    | exact resolve eq21 eq50872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq51144 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq50872 eq66
    | (have r₁ := eq66
       have r₂ := eq50872
       grind)
    | exact resolve eq66 eq50872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq51208 : y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq50872 eq669
    | exact resolve eq669 eq50872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq51251 : y = (k y (M.op x y)) := by
    first
    | exact superpose eq50872 eq3922
    | exact resolve eq3922 eq50872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq51260 : x = (M.op y y) ∨ y = (k x y) := by grind
  clear eq51144
  have eq51264 : y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq51251
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51251
    | exact resolve eq51251 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51251
  have eq51304 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq51208
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51208
    | exact resolve eq51208 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq51208
  have eq51367 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq51140
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq51140
    | exact resolve eq51140 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51140
  have eq51371 : y = (k y y) := by
    first
    | exact superpose eq50872 eq51264
    | exact resolve eq51264 eq50872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51264
  have eq51376 : y = (M.op y y) := by
    first
    | exact superpose eq50872 eq51304
    | exact resolve eq51304 eq50872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50872 eq51304
  have eq51403 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq51367 eq27
    | exact resolve eq27 eq51367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq51437 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq51367 eq624
    | exact resolve eq624 eq51367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq51644 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq481 y y
       have i₂ := eq51371
       grind)
    | exact superpose eq51371 eq481
    | (have j0 := eq481 y y
       grind)
    | exact resolve eq481 eq51371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51371
  have eq51647 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq51644
  have eq51648 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq51647
  have eq51654 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq51648
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq51648
    | exact resolve eq51648 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51648
  have eq51671 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq51367 eq51654
    | exact resolve eq51654 eq51367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51654
  have eq51992 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq51437 eq14
    | exact resolve eq14 eq51437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52021 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51671 eq51992
    | exact resolve eq51992 eq51671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51992
  have eq52036 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51671 eq52021
    | exact resolve eq52021 eq51671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52021
  have eq52117 : ∀ X0 : G, (M.op (σ x) (σ (M.op x y))) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq52036 eq3055
    | exact resolve eq3055 eq52036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055 eq52036
  have eq52127 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq51403 eq52117
    | exact resolve eq52117 eq51403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52117
  have eq55949 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq51260
       have i₂ := eq51376
       grind)
    | exact superpose eq51376 eq51260
    | exact resolve eq51260 eq51376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51260 eq51376
  have eq55968 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq481 x y
       have i₂ := eq55949
       grind)
    | exact superpose eq55949 eq481
    | (have j0 := eq481 x y
       grind)
    | exact resolve eq481 eq55949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq55949
  have eq55971 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq55968
  have eq55978 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq55971
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq55971
    | exact resolve eq55971 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55971
  have eq55993 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq51367 eq55978
    | exact resolve eq55978 eq51367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55978
  have eq56007 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq55993
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq55993
    | exact resolve eq55993 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55993
  have eq56019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq51403 eq56007
    | exact resolve eq56007 eq51403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51403 eq56007
  have eq56024 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq56019
       have r₂ := eq28
       grind)
    | exact resolve eq56019 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56019
  have eq56027 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq56024
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq56024
    | exact resolve eq56024 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56024
  have eq56030 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq51367 eq56027
    | exact resolve eq56027 eq51367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56027
  have eq56033 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq51671 eq56030
    | exact resolve eq56030 eq51671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51671 eq56030
  have eq56036 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq56033
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq56033
    | exact resolve eq56033 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56033
  have eq56586 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | exact superpose eq56036 eq51437
    | exact resolve eq51437 eq56036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56036
  have eq56594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq52127 eq56586
    | exact resolve eq56586 eq52127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56586
  have eq56652 : x = y := by
    first
    | (have r₁ := eq56594
       have r₂ := eq28
       grind)
    | exact resolve eq56594 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56594
  have eq56792 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq56652
       grind)
    | exact superpose eq56652 eq25
    | exact resolve eq25 eq56652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq56652
  have eq57093 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq51367 eq56792
    | exact resolve eq56792 eq51367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51367 eq56792
  have eq57216 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq57093
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57093
    | exact resolve eq57093 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq57093
  have eq57419 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq57216 eq51437
    | exact resolve eq51437 eq57216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51437 eq57216
  have eq57426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52127 eq57419
    | exact resolve eq57419 eq52127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52127 eq57419
  have eq57483 : False := by grind
  exact eq57483

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq140 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq144 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq140 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq140 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq140 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq140 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq664 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq144
  have eq674 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq664 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq1338 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq674 (σ X1) (σ X0)
       grind)
    | exact superpose eq674 eq15
    | exact resolve eq15 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1351 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1338 X0 X1
       have i₂ := eq674 X1 X0
       grind)
    | exact superpose eq674 eq1338
    | exact resolve eq1338 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq1338
  have eq1363 : False := by grind
  exact eq1363
