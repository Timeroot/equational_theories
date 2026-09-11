import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq68 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq65 X1 X2 (σ X0)
       grind)
    | exact superpose eq65 eq28
    | exact resolve eq28 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq69 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq65 X1 X2 (τ X0)
       grind)
    | exact superpose eq65 eq17
    | exact resolve eq17 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq65
  have eq70 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq141 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq61 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq178 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 x (M.op X0 X0)
       have i₂ := eq141 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq141 eq9
    | exact resolve eq9 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq314 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq314 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq314
    | (have j0 := eq314 (σ X0) (σ X1)
       grind)
    | exact resolve eq314 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 ∨ (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X2 X0 X1
       have i₂ := eq314 X2 (σ (M.op (M.op X0 (M.op X1 X0)) X1))
       grind)
    | exact superpose eq314 eq70
    | (have j1 := eq314 X2 (σ (M.op (M.op X0 (M.op X1 X0)) X1))
       grind)
    | exact resolve eq70 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq444 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 ∨ (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X2 X0 X1
       have i₂ := eq314 X2 (τ (M.op (M.op X0 (M.op X1 X0)) X1))
       grind)
    | exact superpose eq314 eq71
    | (have j1 := eq314 X2 (τ (M.op (M.op X0 (M.op X1 X0)) X1))
       grind)
    | exact resolve eq71 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq457 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq444 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq464 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq436 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq1943 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq409 X1 X0
       have i₂ := eq314 X1 X0
       grind)
    | exact superpose eq314 eq409
    | (have j0 := eq409 X1 X0
       have j1 := eq314 (σ X1) (σ X0)
       grind)
    | exact resolve eq409 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq409
  have eq28634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1943 x y
       grind)
    | exact superpose eq1943 eq16
    | (have j1 := eq1943 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1943 x y
       grind)
    | exact resolve eq16 eq1943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq28779 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq28634
  have eq28833 : ∀ X0 : G, (M.op (τ (M.op (M.op (σ y) (σ y)) (σ x))) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq457 (σ y) (σ x) X0
       have i₂ := eq28779
       grind)
    | exact superpose eq28779 eq457
    | exact resolve eq457 eq28779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq28779
  have eq28848 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28833 X0
       have i₂ := eq178 (σ y) (σ x)
       grind)
    | (have i₁ := eq28833 X0
       have i₂ := eq178 X0 (M.op (M.op (σ y) (σ y)) (σ x))
       grind)
    | exact superpose eq178 eq28833
    | exact resolve eq28833 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28833
  have eq28862 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28848 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28848
    | exact resolve eq28848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28848
  have eq28930 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq28862 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28862
  have eq28931 : y = (M.op x y) := by grind
  clear eq28930
  have eq28952 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28931
       grind)
    | exact superpose eq28931 eq16
    | exact resolve eq16 eq28931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28969 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq464 y x X0
       have i₂ := eq28931
       grind)
    | exact superpose eq28931 eq464
    | exact resolve eq464 eq28931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq28931
  have eq28977 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28969 X0
       have i₂ := eq178 y x
       grind)
    | (have i₁ := eq28969 X0
       have i₂ := eq178 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq178 eq28969
    | exact resolve eq28969 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq28969
  have eq29337 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq28952
       have i₂ := eq28977 (σ y)
       grind)
    | exact superpose eq28977 eq28952
    | (have r₁ := eq28952
       have r₂ := eq28977 (σ y)
       grind)
    | exact resolve eq28952 eq28977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28952 eq28977
  have eq29526 : False := by grind
  exact eq29526

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_y_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 X1 X2 (σ X0)
       grind)
    | exact superpose eq35 eq30
    | exact resolve eq30 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq81 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq35
  have eq85 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq86 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq95 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 ∨ (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))
       have i₂ := eq85 X0 X1 X2
       grind)
    | exact superpose eq85 eq58
    | (have j0 := eq58 X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))
       grind)
    | exact resolve eq58 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq95 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq135 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 ∨ (M.op (τ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))
       have i₂ := eq86 X0 X1 X2
       grind)
    | exact superpose eq86 eq58
    | (have j0 := eq58 X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))
       grind)
    | exact resolve eq58 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq136 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq135 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq153 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq24 (M.op X0 X0) x x X3
       have i₂ := eq23 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq24
  have eq212 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq271 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96 X2 X0 (M.op X1 X1)
       have i₂ := eq153 X1 X0
       grind)
    | exact superpose eq153 eq96
    | exact resolve eq96 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq290 : ∀ X1 X2 : G, (M.op (σ (M.op X1 X1)) X2) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq271 x X1 X2
       have i₂ := eq153 x (M.op X1 X1)
       grind)
    | (have i₁ := eq271 x X1 X2
       have i₂ := eq153 x (M.op (M.op x x) (M.op X1 X1))
       grind)
    | exact superpose eq153 eq271
    | exact resolve eq271 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq554 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq212
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq212
    | (have j1 := eq58 (σ y) (σ x)
       grind)
    | exact resolve eq212 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq212
  have eq555 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq554
  have eq3003 : ∀ X0 : G, (M.op (M.op (M.op y y) x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq555
       grind)
    | exact superpose eq555 eq9
    | exact resolve eq9 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq3028 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3003 X0
       have i₂ := eq153 y x
       grind)
    | (have i₁ := eq3003 X0
       have i₂ := eq153 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq153 eq3003
    | exact resolve eq3003 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq26027 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (σ y) (σ y)) (σ x))) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 (σ y) (σ x)
       have i₂ := eq3028 X1
       grind)
    | exact superpose eq3028 eq136
    | (have j1 := eq3028 X1
       grind)
    | exact resolve eq136 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq3028
  have eq26051 : ∀ X0 X1 : G, (M.op (τ (σ x)) X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26027 X0 X1
       have i₂ := eq153 (σ y) (σ x)
       grind)
    | (have i₁ := eq26027 X0 X1
       have i₂ := eq153 X0 (M.op (M.op (σ y) (σ y)) (σ x))
       grind)
    | exact superpose eq153 eq26027
    | (have j0 := eq26027 X0 X1
       grind)
    | exact resolve eq26027 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq26027
  have eq26065 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26051 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26051
    | (have j0 := eq26051 X0 X0
       grind)
    | exact resolve eq26051 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26051
  have eq26564 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26065 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26065
  have eq26565 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26564
  have eq26644 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq290 x X0
       have i₂ := eq26565 x
       grind)
    | exact superpose eq26565 eq290
    | exact resolve eq290 eq26565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq26936 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26644 (σ y)
       grind)
    | exact superpose eq26644 eq16
    | exact resolve eq16 eq26644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26644
  have eq27153 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq26936
       have i₂ := eq26565 y
       grind)
    | exact superpose eq26565 eq26936
    | exact resolve eq26936 eq26565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26565 eq26936
  have eq27154 : False := by grind
  exact eq27154

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq16 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq16 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq178 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq180 : ∀ X0 : G, (M.op (M.op y (M.op x y)) x) ≠ (M.op (M.op y (M.op x y)) x) ∨ (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | exact superpose eq174 eq13
    | (have j0 := eq13 X0 (M.op (M.op y (M.op x y)) x)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq174 (M.op (M.op y (M.op x y)) x)
       grind)
    | exact resolve eq13 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq183 : ∀ X0 : G, (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       have r₂ := eq175 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq187 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq327 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op y (M.op x y)) x))) := by
    intro X0
    first
    | exact superpose eq183 eq34
    | exact resolve eq34 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq183
  have eq357 : ∀ X0 : G, (k X0 (σ (M.op (M.op y (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq327 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq327
    | exact resolve eq327 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq396 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq723 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq724 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq853 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq179 X1 X2 (σ X0)
       grind)
    | exact superpose eq179 eq396
    | exact resolve eq396 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq396
  have eq870 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq853 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq853
    | exact resolve eq853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1255 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq723
       grind)
    | exact superpose eq723 eq39
    | exact resolve eq39 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1256 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1255
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1255
    | exact resolve eq1255 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1258 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1256
    | exact resolve eq1256 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1548 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq182
  have eq1607 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op (M.op X0 X0) (M.op X2 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq870 X1 X0 (M.op X2 X2)
       have i₂ := eq1548 X2 X0
       grind)
    | exact superpose eq1548 eq870
    | exact resolve eq870 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1623 : ∀ X1 X2 : G, (k X1 (τ (M.op X2 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq1607 x X1 X2
       have i₂ := eq1548 x (M.op X2 X2)
       grind)
    | exact superpose eq1548 eq1607
    | exact resolve eq1607 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq4120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1258 eq724
    | exact resolve eq724 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq4129 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4120
       have r₂ := eq27
       grind)
    | exact resolve eq4120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120
  have eq4146 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4129 eq1623
    | exact resolve eq1623 eq4129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623 eq4129
  have eq4222 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq4146
    | exact resolve eq4146 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4146
  have eq4233 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4222 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq4222 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq4222 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4222
  have eq4249 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq723
       have i₂ := eq4233 y
       grind)
    | exact superpose eq4233 eq723
    | exact resolve eq723 eq4233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq4233
  have eq4255 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4249
  have eq4280 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1548 x X0
       have i₂ := eq4255
       grind)
    | exact superpose eq4255 eq1548
    | exact resolve eq1548 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4255
  have eq4437 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4280 y
       grind)
    | exact superpose eq4280 eq18
    | (have j1 := eq4280 y
       grind)
    | exact resolve eq18 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280
  have eq4520 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4437
  have eq4566 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4520 eq27
    | exact resolve eq27 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4570 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (σ y)) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4520 eq187
    | exact resolve eq187 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq4520
  have eq4625 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4570 X0
       have i₂ := eq1548 sF3 sF2
       grind)
    | exact superpose eq1548 eq4570
    | exact resolve eq4570 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4570
  have eq4662 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4625 eq1258
    | exact resolve eq1258 eq4625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq4625
  have eq4667 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq4662
  have eq4676 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4667
       have r₂ := eq4566
       grind)
    | exact resolve eq4667 eq4566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4566 eq4667
  have eq4870 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1548 x X0
       have i₂ := eq4676
       grind)
    | exact superpose eq4676 eq1548
    | exact resolve eq1548 eq4676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4676
  have eq4969 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4870 y
       grind)
    | exact superpose eq4870 eq18
    | (have j1 := eq4870 y
       grind)
    | exact resolve eq18 eq4870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4870
  have eq5052 : y = (M.op x y) := by grind
  clear eq4969
  have eq5099 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5052
       grind)
    | exact superpose eq5052 eq24
    | exact resolve eq24 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq5113 : ∀ X0 : G, (k X0 (σ (M.op (M.op (M.op x y) (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq5052
       grind)
    | exact superpose eq5052 eq357
    | exact resolve eq357 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq5052
  have eq5161 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5113 X0
       have i₂ := eq1548 sF0 x
       grind)
    | exact superpose eq1548 eq5113
    | exact resolve eq5113 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5113
  have eq5181 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5161 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5161
    | (have j0 := eq5161 X0
       grind)
    | exact resolve eq5161 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5161
  have eq5187 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5099 eq20
    | exact resolve eq20 eq5099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5099
  have eq5980 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5181 eq770
    | (have j0 := eq770 (σ x)
       grind)
    | (have r₁ := eq770 (σ x)
       have r₂ := eq5181 (σ x)
       grind)
    | exact resolve eq770 eq5181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq5181
  have eq6000 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5980
  have eq6026 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq6000 eq1548
    | exact resolve eq1548 eq6000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq6000
  have eq6121 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6026 eq26
    | (have j1 := eq6026 (σ y)
       grind)
    | exact resolve eq26 eq6026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6026
  have eq6426 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq6121 eq27
    | exact resolve eq27 eq6121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6121
  have eq6489 : False := by grind
  exact eq6489

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_x_y_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq16 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq16 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq178 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq180 : ∀ X0 : G, (M.op (M.op y (M.op x y)) x) ≠ (M.op (M.op y (M.op x y)) x) ∨ (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | exact superpose eq174 eq13
    | (have j0 := eq13 X0 (M.op (M.op y (M.op x y)) x)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq174 (M.op (M.op y (M.op x y)) x)
       grind)
    | exact resolve eq13 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq183 : ∀ X0 : G, (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       have r₂ := eq175 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq187 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq184 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq327 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op y (M.op x y)) x))) := by
    intro X0
    first
    | exact superpose eq183 eq34
    | exact resolve eq34 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq183
  have eq357 : ∀ X0 : G, (k X0 (σ (M.op (M.op y (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq327 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq327
    | exact resolve eq327 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq396 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq731 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq732 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq778 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq853 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq179 X1 X2 (σ X0)
       grind)
    | exact superpose eq179 eq396
    | exact resolve eq396 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq396
  have eq870 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq853 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq853
    | exact resolve eq853 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1490 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq731
       grind)
    | exact superpose eq731 eq39
    | exact resolve eq39 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1491 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1490
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1490
    | exact resolve eq1490 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1493 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1491
    | exact resolve eq1491 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1548 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq182
  have eq1607 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op (M.op X0 X0) (M.op X2 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq870 X1 X0 (M.op X2 X2)
       have i₂ := eq1548 X2 X0
       grind)
    | exact superpose eq1548 eq870
    | exact resolve eq870 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1623 : ∀ X1 X2 : G, (k X1 (τ (M.op X2 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq1607 x X1 X2
       have i₂ := eq1548 x (M.op X2 X2)
       grind)
    | exact superpose eq1548 eq1607
    | exact resolve eq1607 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq4584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1493 eq732
    | exact resolve eq732 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq4595 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4584
       have r₂ := eq27
       grind)
    | exact resolve eq4584 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4584
  have eq4612 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4595 eq1623
    | exact resolve eq1623 eq4595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623 eq4595
  have eq4688 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq4612
    | exact resolve eq4612 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4612
  have eq4699 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4688 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq4688 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq4688 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4688
  have eq4717 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq731
       have i₂ := eq4699 y
       grind)
    | exact superpose eq4699 eq731
    | exact resolve eq731 eq4699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq4699
  have eq4723 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4717
  have eq4748 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1548 x X0
       have i₂ := eq4723
       grind)
    | exact superpose eq4723 eq1548
    | exact resolve eq1548 eq4723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq4909 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4748 y
       grind)
    | exact superpose eq4748 eq18
    | (have j1 := eq4748 y
       grind)
    | exact resolve eq18 eq4748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4748
  have eq4995 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4909
  have eq5042 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4995 eq27
    | exact resolve eq27 eq4995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5046 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (σ y)) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4995 eq187
    | exact resolve eq187 eq4995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq4995
  have eq5101 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5046 X0
       have i₂ := eq1548 sF3 sF2
       grind)
    | exact superpose eq1548 eq5046
    | exact resolve eq5046 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5046
  have eq5140 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5101 eq1493
    | exact resolve eq1493 eq5101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493 eq5101
  have eq5145 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq5140
  have eq5154 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5145
       have r₂ := eq5042
       grind)
    | exact resolve eq5145 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042 eq5145
  have eq5354 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1548 x X0
       have i₂ := eq5154
       grind)
    | exact superpose eq5154 eq1548
    | exact resolve eq1548 eq5154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154
  have eq5453 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5354 y
       grind)
    | exact superpose eq5354 eq18
    | (have j1 := eq5354 y
       grind)
    | exact resolve eq18 eq5354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5354
  have eq5539 : y = (M.op x y) := by grind
  clear eq5453
  have eq5820 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5539
       grind)
    | exact superpose eq5539 eq24
    | exact resolve eq24 eq5539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq5834 : ∀ X0 : G, (k X0 (σ (M.op (M.op (M.op x y) (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq5539
       grind)
    | exact superpose eq5539 eq357
    | exact resolve eq357 eq5539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq5539
  have eq5882 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5834 X0
       have i₂ := eq1548 sF0 x
       grind)
    | exact superpose eq1548 eq5834
    | exact resolve eq5834 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5834
  have eq5902 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5882 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5882
    | (have j0 := eq5882 X0
       grind)
    | exact resolve eq5882 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5882
  have eq5908 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5820 eq20
    | exact resolve eq20 eq5820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5820
  have eq6206 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5902 eq779
    | (have j0 := eq779 (σ x)
       grind)
    | (have r₁ := eq779 (σ x)
       have r₂ := eq5902 (σ x)
       grind)
    | exact resolve eq779 eq5902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq5902
  have eq6226 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6206
  have eq6405 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq6226 eq1548
    | exact resolve eq1548 eq6226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq6226
  have eq6501 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6405 eq26
    | (have j1 := eq6405 (σ y)
       grind)
    | exact resolve eq26 eq6405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6405
  have eq6640 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq6501 eq27
    | exact resolve eq27 eq6501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6501
  have eq6703 : False := by grind
  exact eq6703

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq68 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq65 X1 X2 (σ X0)
       grind)
    | exact superpose eq65 eq28
    | exact resolve eq28 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq65 X1 X2 (τ X0)
       grind)
    | exact superpose eq65 eq17
    | exact resolve eq17 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq70 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq85 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (M.op X1 (M.op X2 X1)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))
       have i₂ := eq71 (σ X0) X1 X2
       grind)
    | exact superpose eq71 eq28
    | exact resolve eq28 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq71
  have eq90 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op (M.op X1 (M.op X2 X1)) X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq140 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq61 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq176 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 x (M.op X0 X0)
       have i₂ := eq140 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq140 eq9
    | exact resolve eq9 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq290 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq290
    | (have j0 := eq290 (σ X0) (σ X1)
       grind)
    | exact resolve eq290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq311 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq311
    | (have j0 := eq311 (σ X0) (σ X1)
       grind)
    | exact resolve eq311 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq311 X1 X0
       have i₂ := eq290 X1 X0
       grind)
    | exact superpose eq290 eq311
    | (have j0 := eq311 X1 X0
       have j1 := eq290 (σ X1) (σ X0)
       grind)
    | exact resolve eq311 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 (M.op X2 X1)) X2)) = (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op (M.op X1 (M.op X2 X1)) X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq311 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq65 X1 X2 X0
       grind)
    | exact superpose eq65 eq311
    | (have j0 := eq311 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | exact resolve eq311 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq31350 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq495 x y
       grind)
    | exact superpose eq495 eq16
    | (have j1 := eq495 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq495 x y
       grind)
    | exact resolve eq16 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq31422 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31350
  have eq31444 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31422
       grind)
    | exact superpose eq31422 eq16
    | exact resolve eq16 eq31422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31446 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq31422
       grind)
    | exact superpose eq31422 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq31422
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq31422
       grind)
    | exact resolve eq13 eq31422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31470 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq31446
  have eq31472 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31470
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq31470
    | exact resolve eq31470 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31470
  have eq31473 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq290 eq31472
    | (have j1 := eq290 (σ x) (σ x)
       grind)
    | exact resolve eq31472 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq31472
  have eq31474 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31473
       have r₂ := eq31444
       grind)
    | exact resolve eq31473 eq31444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31473
  have eq31477 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq176 (σ x) X0
       have i₂ := eq31474
       grind)
    | exact superpose eq31474 eq176
    | exact resolve eq176 eq31474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31524 : ∀ X0 : G, (k X0 (τ (τ (M.op (M.op (σ x) (σ x)) (σ x))))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90 X0 (σ x) (σ x)
       have i₂ := eq31474
       grind)
    | exact superpose eq31474 eq90
    | exact resolve eq90 eq31474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq31474
  have eq31554 : ∀ X0 : G, (k X0 (τ (τ (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq31524 X0
       have i₂ := eq176 (σ x) (σ x)
       grind)
    | (have i₁ := eq31524 X0
       have i₂ := eq176 X0 (M.op (M.op (σ x) (σ x)) (σ x))
       grind)
    | exact superpose eq176 eq31524
    | exact resolve eq31524 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31524
  have eq31575 : ∀ X0 : G, (k X0 (τ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq31554 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31554
    | exact resolve eq31554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31554
  have eq31605 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31422
       have i₂ := eq31477 (σ y)
       grind)
    | exact superpose eq31477 eq31422
    | exact resolve eq31422 eq31477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31422 eq31477
  have eq31740 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq31605
  have eq32686 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq493 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq32770 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 (M.op X1 X0)) X1)) ≠ (σ (M.op (M.op X0 (M.op X1 X0)) X1)) ∨ (k X2 (σ (M.op (M.op X0 (M.op X1 X0)) X1))) = (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) ∨ (σ (M.op (M.op X0 (M.op X1 X0)) X1)) = (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) (σ (M.op (M.op X0 (M.op X1 X0)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (σ (M.op (M.op X0 (M.op X1 X0)) X1))
       have i₂ := eq496 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq496 eq12
    | (have j0 := eq12 X2 (σ (M.op (M.op X0 (M.op X1 X0)) X1))
       have j1 := eq496 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))
       have r₂ := eq496 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq32837 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op (M.op X0 (M.op X1 X0)) X1))) = (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) ∨ (σ (M.op (M.op X0 (M.op X1 X0)) X1)) = (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) (σ (M.op (M.op X0 (M.op X1 X0)) X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32770 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32770
  have eq32851 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op (M.op X0 (M.op X1 X0)) X1))) = (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32837 X0 X1 X2
       have j1 := eq12 X2 (σ (M.op (M.op X0 (M.op X1 X0)) X1))
       grind)
    | (have r₁ := eq32837 X0 X1 X2
       have r₂ := eq12 X0 (σ (M.op (M.op X0 (M.op X1 X0)) X1))
       grind)
    | exact resolve eq32837 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32837
  have eq32871 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32851 X0 X1 X2
       have i₂ := eq70 X2 X0 X1
       grind)
    | exact superpose eq70 eq32851
    | exact resolve eq32851 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq32851
  have eq32899 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X0) (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32871 X0 (M.op X1 X1) X2
       have i₂ := eq176 X1 X0
       grind)
    | exact superpose eq176 eq32871
    | exact resolve eq32871 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32871
  have eq33147 : ∀ X1 X2 : G, (M.op (σ (M.op X1 X1)) X2) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq32899 x X1 X2
       have i₂ := eq176 x (M.op X1 X1)
       grind)
    | (have i₁ := eq32899 x X1 X2
       have i₂ := eq176 x (M.op (M.op x x) (M.op X1 X1))
       grind)
    | exact superpose eq176 eq32899
    | exact resolve eq32899 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32899
  have eq96282 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32686 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq32686
    | (have j0 := eq32686 (τ X1) (τ X0)
       grind)
    | exact resolve eq32686 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq32686
  have eq96312 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq96282 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq96282
    | (have j0 := eq96282 X0 X1
       grind)
    | exact resolve eq96282 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96282
  have eq96413 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq96312 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq96312
    | (have j0 := eq96312 X0 X1
       grind)
    | exact resolve eq96312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96312
  have eq96495 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96413 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96413
    | (have j0 := eq96413 X0 X1
       grind)
    | exact resolve eq96413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96413
  have eq96559 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq96495 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96495
    | (have j0 := eq96495 X0 X1
       grind)
    | exact resolve eq96495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96495
  have eq96794 : ∀ X0 : G, (σ X0) ≠ (σ (τ x)) ∨ (σ (τ x)) = (M.op (σ (τ x)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq96559 X0 (τ x)
       have i₂ := eq31575 X0
       grind)
    | exact superpose eq31575 eq96559
    | (have j0 := eq96559 X0 (τ x)
       grind)
    | exact resolve eq96559 eq31575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31575 eq96559
  have eq96844 : ∀ X0 : G, (σ X0) ≠ x ∨ (σ (τ x)) = (M.op (σ (τ x)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq96794 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq96794
    | (have j0 := eq96794 X0
       grind)
    | (have r₁ := eq96794 (τ (σ (τ x)))
       have r₂ := eq11 (σ (τ x))
       grind)
    | exact resolve eq96794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96794
  have eq96951 : ∀ X0 : G, (σ X0) ≠ x ∨ x = (M.op x (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq96844 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq96844
    | (have j0 := eq96844 X0
       grind)
    | (have r₁ := eq96844 (τ x)
       have r₂ := eq11 x
       grind)
    | exact resolve eq96844 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96844
  have eq97285 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq96951 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96951
    | (have r₁ := eq96951 (τ x)
       have r₂ := eq11 x
       grind)
    | exact resolve eq96951 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96951
  have eq97295 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq97285 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97285
  have eq97297 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq97295
       grind)
    | exact superpose eq97295 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq97295
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq97295
       grind)
    | exact resolve eq13 eq97295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97327 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by grind
  clear eq97297
  have eq97328 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq97327
  have eq97334 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq311 y x
       have i₂ := eq97328
       grind)
    | exact superpose eq97328 eq311
    | (have j0 := eq311 y x
       grind)
    | exact resolve eq311 eq97328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq97328
  have eq97337 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq97334
  have eq97344 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97337
       grind)
    | exact superpose eq97337 eq16
    | exact resolve eq16 eq97337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97337
  have eq97379 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq97295 eq97344
    | exact resolve eq97344 eq97295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97295 eq97344
  have eq97380 : x = (M.op x x) := by grind
  clear eq97379
  have eq98030 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq97380
       grind)
    | exact superpose eq97380 eq176
    | exact resolve eq176 eq97380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq97380
  have eq98505 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98030 y
       grind)
    | exact superpose eq98030 eq16
    | exact resolve eq16 eq98030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98506 : x = y ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq31444
       have i₂ := eq98030 y
       grind)
    | exact superpose eq98030 eq31444
    | exact resolve eq31444 eq98030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31444
  have eq98520 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq31740
       have i₂ := eq98030 y
       grind)
    | exact superpose eq98030 eq31740
    | exact resolve eq31740 eq98030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31740
  have eq98567 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33147 x X0
       have i₂ := eq98030 x
       grind)
    | exact superpose eq98030 eq33147
    | exact resolve eq33147 eq98030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33147
  have eq98865 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq98567 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98567
  have eq98866 : (σ x) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq98506
       have i₂ := eq98030 y
       grind)
    | exact superpose eq98030 eq98506
    | exact resolve eq98506 eq98030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98030 eq98506
  have eq98871 : x = y := by
    first
    | (have r₁ := eq98866
       have r₂ := eq98520
       grind)
    | exact resolve eq98866 eq98520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98520 eq98866
  have eq98894 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98505
       have i₂ := eq98871
       grind)
    | exact superpose eq98871 eq98505
    | exact resolve eq98505 eq98871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98505 eq98871
  have eq99783 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq98894
       have i₂ := eq98865 (σ x)
       grind)
    | exact superpose eq98865 eq98894
    | (have r₁ := eq98894
       have r₂ := eq98865 (σ x)
       grind)
    | exact resolve eq98894 eq98865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98865 eq98894
  have eq100005 : False := by grind
  exact eq100005

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq36
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq36
  have eq97 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq105 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq329 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq332 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq329 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq329 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq329 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq329 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq531 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq332 X1 (τ X0)
       grind)
    | exact superpose eq332 eq28
    | (have j1 := eq332 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq28 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq532 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq332 (σ X1) (σ X0)
       grind)
    | exact superpose eq332 eq15
    | (have j1 := eq332 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq20514 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq531 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq531
    | exact resolve eq531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq20596 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20514 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20514
    | (have j0 := eq20514 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq20514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20514
  have eq63199 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq532 x y
       grind)
    | exact superpose eq532 eq16
    | (have j1 := eq532 x y
       grind)
    | exact resolve eq16 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq63829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63199
       have i₂ := eq20596 x y
       grind)
    | exact superpose eq20596 eq63199
    | (have j1 := eq20596 (σ x) (σ y)
       grind)
    | (have r₁ := eq63199
       have r₂ := eq20596 x y
       grind)
    | (have r₁ := eq63199
       have r₂ := eq20596 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq63199
       have r₂ := eq20596 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq63199 eq20596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20596 eq63199
  have eq63830 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq63829
  have eq64256 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq63830
       grind)
    | exact superpose eq63830 eq10
    | exact resolve eq10 eq63830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63830
  have eq64321 : x = y ∨ x = y := by
    first
    | (have i₁ := eq64256
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64256
    | exact resolve eq64256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64256
  have eq64322 : x = y := by grind
  clear eq64321
  have eq64912 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64322
       grind)
    | exact superpose eq64322 eq16
    | exact resolve eq16 eq64322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64322
  have eq64913 : False := by grind
  exact eq64913

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyy_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq104 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X1 X2 (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq104
    | exact resolve eq104 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq104 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq104 eq104
    | exact resolve eq104 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq9 eq104
    | exact resolve eq104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (M.op X1 X1) x X0
       have i₂ := eq104 x (M.op X1 X1) X1
       grind)
    | exact superpose eq104 eq111
    | exact resolve eq111 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq111
  have eq161 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq133
    | exact resolve eq133 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq162 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq133
    | exact resolve eq133 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq133
  have eq1019 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq113 X0 X1 x
       grind)
    | exact superpose eq113 eq9
    | exact resolve eq9 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1534 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1019 X1 x X2
       have i₂ := eq162 X0 x
       grind)
    | exact superpose eq162 eq1019
    | exact resolve eq1019 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq1019
  have eq2272 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq19326 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X1) (τ (M.op X2 X2)))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1534 X2 (σ X1) (σ X0)
       have i₂ := eq2272 X0 X1
       grind)
    | (have i₁ := eq1534 X0 (σ X0) (σ X0)
       have i₂ := eq2272 X0 X1
       grind)
    | exact superpose eq2272 eq1534
    | (have j1 := eq2272 X0 X1
       grind)
    | exact resolve eq1534 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534 eq2272
  have eq19758 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19326 X0 X1 x
       have i₂ := eq109 x (σ X0) (σ X1)
       grind)
    | exact superpose eq109 eq19326
    | (have j0 := eq19326 X0 X1 x
       grind)
    | exact resolve eq19326 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq19326
  have eq19759 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq19758 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19758
  have eq21363 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq19759 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19759
  have eq23177 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq21363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21363
  have eq24823 : ∀ X0 X3 : G, (σ (k X0 X3)) = (M.op (σ X0) (σ X3)) ∨ (σ X0) = (σ X3) := by
    intro X0 X3
    first
    | (have j0 := eq23177 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23177
  have eq24899 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq24823 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24823
  have eq24902 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24899 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq24899
    | (have j0 := eq24899 (τ X0) (τ X1)
       grind)
    | exact resolve eq24899 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq24933 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24902 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq24902
    | (have j0 := eq24902 X0 X1
       grind)
    | exact resolve eq24902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24902
  have eq24946 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24933 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24933
    | (have j0 := eq24933 X0 X1
       grind)
    | exact resolve eq24933 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24933
  have eq24947 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24946 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq24946
    | (have j0 := eq24946 X0 X1
       grind)
    | exact resolve eq24946 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24946
  have eq24948 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24947 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq24947
    | (have j0 := eq24947 X0 X1
       grind)
    | exact resolve eq24947 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24947
  have eq24949 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24948 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24948
    | (have j0 := eq24948 X0 X1
       grind)
    | exact resolve eq24948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24948
  have eq24953 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24899 X0 X1
       have i₂ := eq24949 X0 X1
       grind)
    | exact superpose eq24949 eq24899
    | (have j0 := eq24899 X0 X1
       have j1 := eq24949 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq24899 eq24949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24899 eq24949
  have eq853340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24953 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24953
  have eq853663 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq853340 x y
       grind)
    | exact superpose eq853340 eq16
    | (have j1 := eq853340 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq853340 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq853340 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq853340 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq853340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853340
  have eq853831 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq853663
  have eq853860 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq853831
       grind)
    | exact superpose eq853831 eq10
    | exact resolve eq10 eq853831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853831
  have eq853991 : x = y ∨ x = y := by
    first
    | (have i₁ := eq853860
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq853860
    | exact resolve eq853860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853860
  have eq853992 : x = y := by grind
  clear eq853991
  have eq853993 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq853992
       grind)
    | exact superpose eq853992 eq16
    | exact resolve eq16 eq853992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853992
  have eq853994 : False := by grind
  exact eq853994

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_y_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq104 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X1 X2 (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq104
    | exact resolve eq104 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq104 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq104 eq104
    | exact resolve eq104 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq9 eq104
    | exact resolve eq104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (M.op X1 X1) x X0
       have i₂ := eq104 x (M.op X1 X1) X1
       grind)
    | exact superpose eq104 eq111
    | exact resolve eq111 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq111
  have eq161 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq133
    | exact resolve eq133 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq162 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq133
    | exact resolve eq133 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq133
  have eq361 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1236 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq113 X0 X1 x
       grind)
    | exact superpose eq113 eq9
    | exact resolve eq9 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1990 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1236 X1 x X2
       have i₂ := eq162 X0 x
       grind)
    | exact superpose eq162 eq1236
    | exact resolve eq1236 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq1236
  have eq20981 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X1) (τ (M.op X2 X2)))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1990 X2 (σ X1) (σ X0)
       have i₂ := eq361 X0 X1
       grind)
    | (have i₁ := eq1990 X0 (σ X0) (σ X0)
       have i₂ := eq361 X0 X1
       grind)
    | exact superpose eq361 eq1990
    | (have j1 := eq361 X0 X1
       grind)
    | exact resolve eq1990 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq1990
  have eq21430 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20981 X0 X1 x
       have i₂ := eq109 x (σ X0) (σ X1)
       grind)
    | exact superpose eq109 eq20981
    | (have j0 := eq20981 X0 X1 x
       grind)
    | exact resolve eq20981 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq20981
  have eq21431 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq21430 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21430
  have eq23227 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq21431 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21431
  have eq23230 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23227 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq23227
    | (have j0 := eq23227 (τ X0) (τ X1)
       grind)
    | exact resolve eq23227 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq23261 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23230 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq23230
    | (have j0 := eq23230 X0 X1
       grind)
    | exact resolve eq23230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23230
  have eq23274 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23261 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23261
    | (have j0 := eq23261 X0 X1
       grind)
    | exact resolve eq23261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23261
  have eq23275 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23274 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq23274
    | (have j0 := eq23274 X0 X1
       grind)
    | exact resolve eq23274 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23274
  have eq23276 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23275 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq23275
    | (have j0 := eq23275 X0 X1
       grind)
    | exact resolve eq23275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23275
  have eq23277 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23276 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23276
    | (have j0 := eq23276 X0 X1
       grind)
    | exact resolve eq23276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23276
  have eq23280 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23227 X0 X1
       have i₂ := eq23277 X0 X1
       grind)
    | exact superpose eq23277 eq23227
    | (have j0 := eq23227 X0 X1
       have j1 := eq23277 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq23227 eq23277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23227 eq23277
  have eq915481 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq23280 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23280
  have eq915832 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq915481 x y
       grind)
    | exact superpose eq915481 eq16
    | (have j1 := eq915481 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq915481 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq915481 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq915481 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq915481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915481
  have eq915998 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq915832
  have eq916029 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq915998
       grind)
    | exact superpose eq915998 eq10
    | exact resolve eq10 eq915998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915998
  have eq916172 : x = y ∨ x = y := by
    first
    | (have i₁ := eq916029
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq916029
    | exact resolve eq916029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916029
  have eq916173 : x = y := by grind
  clear eq916172
  have eq916174 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq916173
       grind)
    | exact superpose eq916173 eq16
    | exact resolve eq16 eq916173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916173
  have eq916175 : False := by grind
  exact eq916175
