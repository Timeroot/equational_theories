import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq51
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq61
  have eq119 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq123 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       have j1 := eq64 X0 X1
       grind)
    | (have r₁ := eq119 X0 X1
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq119 X0 X0
       have r₂ := eq64 X0 X0
       grind)
    | exact resolve eq119 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq119
  have eq364 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq123 (σ X0) (σ X1)
       grind)
    | exact superpose eq123 eq15
    | exact resolve eq15 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 X1
       have i₂ := eq123 X0 X1
       grind)
    | exact superpose eq123 eq364
    | exact resolve eq364 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq364
  have eq371 : False := by grind
  exact eq371

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_pyx_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq48 (τ X0)
       grind)
    | exact superpose eq48 eq18
    | (have j1 := eq48 (τ X0)
       grind)
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq48
  have eq90 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq115 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq26
    | exact resolve eq26 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq290 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61 x y
       grind)
    | exact superpose eq61 eq16
    | (have j1 := eq61 x y
       grind)
    | exact resolve eq16 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq351 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq36
    | (have j1 := eq90 X0
       grind)
    | exact resolve eq36 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq365 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq351 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq351
    | (have j0 := eq351 X0
       grind)
    | exact resolve eq351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq366 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq365 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq368 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq366 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq366
    | exact resolve eq366 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq10
    | exact resolve eq10 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq368
    | exact resolve eq368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq394 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq10
    | exact resolve eq10 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq394 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq394
    | exact resolve eq394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq442 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0
       have i₂ := eq115 (τ X0) X1
       grind)
    | (have i₁ := eq36 X0
       have i₂ := eq115 (τ X0) (τ X0)
       grind)
    | exact superpose eq115 eq36
    | exact resolve eq36 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq115
  have eq455 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) X1) (τ X0))) = (k (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 X1
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq442
    | exact resolve eq442 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq442
  have eq463 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq421 (σ X0)
       grind)
    | exact superpose eq421 eq15
    | exact resolve eq15 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq463 X0
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq463
    | exact resolve eq463 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq495 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq421 X0
       grind)
    | exact superpose eq421 eq372
    | exact resolve eq372 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq501 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq495 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq495
    | exact resolve eq495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq730 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq290
       have i₂ := eq478 y
       grind)
    | exact superpose eq478 eq290
    | exact resolve eq290 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq731 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq730
       have i₂ := eq478 x
       grind)
    | exact superpose eq478 eq730
    | exact resolve eq730 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq732 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq731
       have i₂ := eq478 y
       grind)
    | exact superpose eq478 eq731
    | exact resolve eq731 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq732
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq732
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq732 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq734 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq733
  have eq1011 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq421 X0
       grind)
    | exact superpose eq421 eq455
    | exact resolve eq455 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq1175 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1011 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1011
    | exact resolve eq1011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq1011 (σ X0) X1
       grind)
    | exact superpose eq1011 eq23
    | exact resolve eq23 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1232 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1186 X0 X1
       have i₂ := eq10 (M.op (M.op (τ (σ X0)) X1) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq1186
    | exact resolve eq1186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1240 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    grind
  clear eq1175
  have eq1252 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1232 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1232
    | exact resolve eq1232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1256 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1240 X0 X1
       have i₂ := eq478 X0
       grind)
    | exact superpose eq478 eq1240
    | exact resolve eq1240 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1263 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1252 X0 X1
       have i₂ := eq501 X0
       grind)
    | exact superpose eq501 eq1252
    | exact resolve eq1252 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1304 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq1263 (σ X0) X1
       grind)
    | exact superpose eq1263 eq23
    | exact resolve eq23 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1263
  have eq1329 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (τ (M.op (M.op (σ X0) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1304 X0 X1
       have i₂ := eq501 X0
       grind)
    | exact superpose eq501 eq1304
    | exact resolve eq1304 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq1304
  have eq3980 : ∀ X0 X1 : G, (k (M.op (k X0 X0) (k X0 X0)) (k X0 X0)) = (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1329 (k X0 X0) X1
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq1329
    | exact resolve eq1329 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq4112 : ∀ X0 X1 : G, (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0)))) = (M.op (M.op (k X0 X0) (k X0 X0)) (k X0 X0)) := by
    intro X0 X1
    grind
  clear eq3980
  have eq4163 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4112 X0 X1
       have i₂ := eq421 X0
       grind)
    | exact superpose eq421 eq4112
    | exact resolve eq4112 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq4112
  have eq4190 : ∀ X0 X1 : G, (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4163 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq4163
    | exact resolve eq4163 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4163
  have eq10506 : (M.op y y) = (τ (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq734
       grind)
    | exact superpose eq734 eq10
    | exact resolve eq10 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq10569 : x = (M.op y y) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10506
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10506
    | exact resolve eq10506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10506
  have eq10570 : x = (M.op y y) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq10569
  have eq207795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1256 y y
       have i₂ := eq10570
       grind)
    | exact superpose eq10570 eq1256
    | exact resolve eq1256 eq10570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256 eq10570
  have eq207882 : (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq207795
       have r₂ := eq16
       grind)
    | exact resolve eq207795 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207795
  have eq209592 : ∀ X0 : G, y = (M.op (M.op (M.op x x) X0) (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq9 y x y
       have i₂ := eq207882
       grind)
    | exact superpose eq207882 eq9
    | exact resolve eq9 eq207882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207882
  have eq209693 : x = y ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq209592 x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq209592
    | exact resolve eq209592 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209592
  have eq211169 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq209693
       grind)
    | exact superpose eq209693 eq16
    | exact resolve eq16 eq209693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209693
  have eq211170 : (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq211169
       have r₂ := eq478 x
       grind)
    | exact resolve eq211169 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211169
  have eq211219 : ∀ X0 : G, y = (τ (M.op (M.op (σ (M.op x x)) X0) (σ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq4190 y x
       have i₂ := eq211170
       grind)
    | exact superpose eq211170 eq4190
    | exact resolve eq4190 eq211170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4190 eq211170
  have eq211606 : y = (k (M.op (M.op x x) (M.op x x)) (M.op x x)) := by
    first
    | (have i₁ := eq211219 x
       have i₂ := eq1329 (M.op x x) x
       grind)
    | exact superpose eq1329 eq211219
    | exact resolve eq211219 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329 eq211219
  have eq211628 : y = (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) := by grind
  clear eq211606
  have eq211641 : x = y := by
    first
    | (have i₁ := eq211628
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq211628
    | exact resolve eq211628 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211628
  have eq211651 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211641
       grind)
    | exact superpose eq211641 eq16
    | exact resolve eq16 eq211641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211641
  have eq211652 : False := by grind
  exact eq211652

/-- `Equation2055`: `x = ((x ◇ y) ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_x_pyx_pxy_Equation2055 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2055 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2055.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X1 X2)) = X0 := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 (M.op (M.op X0 X1) X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X0) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) X0) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X1) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq72 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq75 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq75
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq83
    | exact resolve eq83 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq128 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq151 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq210 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) x)) X0) x) = X0 := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (M.op (M.op X0 X1) X0) (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq60 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60
    | (have j0 := eq60 x y
       grind)
    | exact resolve eq60 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq60
    | (have j0 := eq60 (σ x) (σ y)
       grind)
    | exact resolve eq60 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) X2
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq60 X0 X0
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 (M.op (M.op X0 (M.op X1 X2)) X0) X2
       have i₂ := eq14 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq14 eq63
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) X1 X3
       have i₂ := eq63 X1 X0 X2
       grind)
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59 X0 (M.op X0 X1) X2 X3
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq59
    | exact resolve eq59 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x)))) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op x y) x)) X0)) (M.op x X2)) := by
    intro X0 X2
    first
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq511 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0)) (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 (M.op (M.op X0 X1) X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (M.op X0 (M.op (M.op X0 X1) X0)) x
       have i₂ := eq59 X0 X1 x X1
       grind)
    | exact superpose eq59 eq63
    | exact resolve eq63 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq701 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq1014 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq60 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x)
       have i₂ := eq223 X0 x x
       grind)
    | exact superpose eq223 eq60
    | exact resolve eq60 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1014 X0
       have i₂ := eq223 X0 X0 X0
       grind)
    | exact superpose eq223 eq1014
    | exact resolve eq1014 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1250 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq224 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3664 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))))) (σ x)) := by
    first
    | (have i₁ := eq522 (M.op (M.op sF4 sF4) sF4)
       have i₂ := eq1018 sF4
       grind)
    | exact superpose eq1018 eq522
    | exact resolve eq522 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3689 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3664
       have i₂ := eq14 sF4 sF4 (M.op (M.op sF4 sF4) sF4)
       grind)
    | exact superpose eq14 eq3664
    | exact resolve eq3664 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3664
  have eq3707 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3689 eq522
    | exact resolve eq522 eq3689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq3689
  have eq3727 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq3707 eq14
    | exact resolve eq14 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3744 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq703 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq703
    | (have j0 := eq703 (τ X0)
       grind)
    | exact resolve eq703 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq703
  have eq3752 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3744 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3744
    | (have j0 := eq3744 X0
       grind)
    | exact resolve eq3744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744
  have eq3758 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3752 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3752
    | (have j0 := eq3752 X0
       grind)
    | exact resolve eq3752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3752
  have eq3911 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3727 eq62
    | exact resolve eq62 eq3727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq3727
  have eq3934 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3911 eq3707
    | exact resolve eq3707 eq3911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3911
  have eq5182 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq406 (M.op (M.op X0 X0) X0) (M.op X0 X1) x
       have i₂ := eq223 X0 X1 x
       grind)
    | exact superpose eq223 eq406
    | exact resolve eq406 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq5272 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5182 X0 X1
       have i₂ := eq14 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq14 eq5182
    | exact resolve eq5182 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5182
  have eq5282 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5272 X0 x
       have i₂ := eq60 X0 x
       grind)
    | exact superpose eq60 eq5272
    | exact resolve eq5272 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5272
  have eq5986 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq492 X0 X1 X2 X3
       have i₂ := eq5282 X0
       grind)
    | exact superpose eq5282 eq492
    | exact resolve eq492 eq5282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq6099 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq5986 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x) X3 X4
       have i₂ := eq223 X0 x x
       grind)
    | exact superpose eq223 eq5986
    | exact resolve eq5986 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5986
  have eq6280 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6099 x X3 X4
       have i₂ := eq217 x x
       grind)
    | exact superpose eq217 eq6099
    | exact resolve eq6099 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq6099
  have eq6320 : ∀ X0 X3 X4 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6280 X0 X3 X4
       have i₂ := eq1018 X0
       grind)
    | exact superpose eq1018 eq6280
    | exact resolve eq6280 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6280
  have eq6335 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6320 X0 X3 X4
       have i₂ := eq5282 X0
       grind)
    | exact superpose eq5282 eq6320
    | exact resolve eq6320 eq5282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5282 eq6320
  have eq6400 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq6335
    | (have j0 := eq6335 (σ x) (σ y) X0
       grind)
    | exact resolve eq6335 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6662 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op X0 X0) (M.op x X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq510 x X2
       have i₂ := eq6335 x (M.op sF0 x) x
       grind)
    | exact superpose eq6335 eq510
    | exact resolve eq510 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq6683 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op x X1)) x) = X0 := by
    intro X0 X1
    first
    | exact superpose eq6662 eq210
    | exact resolve eq210 eq6662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq6662
  have eq6819 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq6683 X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq6683
    | (have j0 := eq6683 X0 y
       grind)
    | exact resolve eq6683 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6683
  have eq6866 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq6819 (M.op (M.op X0 X0) X0)
       have i₂ := eq223 X0 X0 X0
       grind)
    | exact superpose eq223 eq6819
    | exact resolve eq6819 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6819
  have eq6946 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op X0 X0) (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq511 x X2
       have i₂ := eq6335 x (M.op sF4 sF2) x
       grind)
    | exact superpose eq6335 eq511
    | exact resolve eq511 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq6968 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) X1)) (σ x)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq6946 eq213
    | exact resolve eq213 eq6946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq6946
  have eq7106 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq6968
    | (have j0 := eq6968 X0 (σ y)
       grind)
    | exact resolve eq6968 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6968
  have eq7152 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7106 (M.op (M.op X0 X0) X0)
       have i₂ := eq223 X0 X0 X0
       grind)
    | exact superpose eq223 eq7106
    | exact resolve eq7106 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq7106
  have eq7589 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) := by
    first
    | exact superpose eq3707 eq6866
    | exact resolve eq6866 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3707
  have eq7592 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1018 X0
       have i₂ := eq6866 X0
       grind)
    | exact superpose eq6866 eq1018
    | exact resolve eq1018 eq6866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq6866
  have eq8064 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq72
    | (have j0 := eq72 x
       grind)
    | exact resolve eq72 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq8088 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8064
  have eq8098 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8088
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq8088
    | exact resolve eq8088 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq8088
  have eq8389 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (σ x) (σ y)))) (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7152 eq14
    | exact resolve eq14 eq7152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7152
  have eq8413 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8389 X1 X1
       have i₂ := eq14 X1 X1 sF4
       grind)
    | exact superpose eq14 eq8389
    | exact resolve eq8389 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8389
  have eq10186 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ X0)) X1) (σ (k X0 (M.op x y)))) = X1 ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq208 eq14
    | (have j1 := eq208 X0
       grind)
    | exact resolve eq14 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq12376 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq8413 eq497
    | exact resolve eq497 eq8413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq8413
  have eq12377 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3934 eq12376
    | exact resolve eq12376 eq3934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3934 eq12376
  have eq12378 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7589 eq12377
    | exact resolve eq12377 eq7589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7589 eq12377
  have eq12379 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq6400 eq12378
    | exact resolve eq12378 eq6400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6400 eq12378
  have eq12418 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (σ y)) := by
    first
    | (have i₁ := eq12379 (M.op (M.op x x) x) sF3 x
       have i₂ := eq63 x sF3 x
       grind)
    | exact superpose eq63 eq12379
    | exact resolve eq12379 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12379
  have eq12495 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq530 x x
       have i₂ := eq6335 x x x
       grind)
    | exact superpose eq6335 eq530
    | exact resolve eq530 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq12724 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op (M.op (M.op (σ X0) X1) (σ X0)) (σ (k X0 X0))) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12495 (σ X1) X1
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq12495
    | (have j1 := eq71 X0 X0
       grind)
    | exact resolve eq12495 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq12495
  have eq12781 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op (M.op (M.op (σ X0) X1) (σ X0)) (σ (k X0 X0))) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq12724 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12724
  have eq14072 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) = (M.op (M.op X0 X0) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq411 X0 X1 X2 X3
       have i₂ := eq6335 X0 (M.op (M.op X1 X2) X1) X0
       grind)
    | exact superpose eq6335 eq411
    | exact resolve eq411 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq6335
  have eq14355 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 X0 x
       have i₂ := eq14072 X0 X1 x X2
       grind)
    | exact superpose eq14072 eq63
    | exact resolve eq63 eq14072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq14072
  have eq24246 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24285 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq50 eq24246
    | exact resolve eq24246 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq24246
  have eq25131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25131
    | exact resolve eq25131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25131
  have eq25149 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq25138
       have r₂ := eq28
       grind)
    | exact resolve eq25138 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25138
  have eq25151 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25149
    | exact resolve eq25149 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25149
  have eq25200 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25151 eq60
    | exact resolve eq60 eq25151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25151
  have eq25234 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25200
    | exact resolve eq25200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25200
  have eq25235 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25234
  have eq25533 : y ≠ y ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq224 x x
       have i₂ := eq25235
       grind)
    | exact superpose eq25235 eq224
    | exact resolve eq224 eq25235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25235
  have eq25554 : x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25533
  have eq25561 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq25554
       have r₂ := eq51
       grind)
    | exact resolve eq25554 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq25554
  have eq25657 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq25561
       grind)
    | exact superpose eq25561 eq45
    | exact resolve eq45 eq25561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq25561
  have eq25680 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25657
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25657
    | exact resolve eq25657 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25657
  have eq25687 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq25680
       have r₂ := eq52
       grind)
    | exact resolve eq25680 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq25680
  have eq25712 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq86 eq25687
    | exact resolve eq25687 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq25724 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25687 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq25687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25687
  have eq25729 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq25724
    | exact resolve eq25724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25724
  have eq25740 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq25729
    | exact resolve eq25729 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25729
  have eq37256 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq60 x x
       have i₂ := eq25712
       grind)
    | exact superpose eq25712 eq60
    | exact resolve eq60 eq25712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25712
  have eq37298 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37256
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37256
    | exact resolve eq37256 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37256
  have eq37299 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq37298
  have eq37317 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37299 eq29
    | exact resolve eq29 eq37299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq37299
  have eq37508 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq37317
    | exact resolve eq37317 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq37317
  have eq37832 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37508 eq21
    | exact resolve eq21 eq37508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37883 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37508 eq220
    | exact resolve eq220 eq37508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq37508
  have eq37960 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37883
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37883
    | exact resolve eq37883 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37883
  have eq38005 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37832
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37832
    | exact resolve eq37832 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37832
  have eq38027 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38005 eq58
    | exact resolve eq58 eq38005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq39174 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq37960
       grind)
    | exact superpose eq37960 eq81
    | exact resolve eq81 eq37960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq37960
  have eq39263 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq39174
  have eq39293 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq39263
    | exact resolve eq39263 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39263
  have eq40445 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8098 eq39293
    | exact resolve eq39293 eq8098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8098
  have eq51002 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25740 eq60
    | exact resolve eq60 eq25740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25740
  have eq51047 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq51002
    | exact resolve eq51002 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51002
  have eq51048 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51047
  have eq51067 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51048 eq28
    | exact resolve eq28 eq51048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51074 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51048 eq221
    | exact resolve eq221 eq51048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq51120 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (M.op x y)) x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51048 eq12418
    | exact resolve eq12418 eq51048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12418 eq51048
  have eq51149 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7592 eq51120
    | exact resolve eq51120 eq7592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7592 eq51120
  have eq51163 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq51074
    | exact resolve eq51074 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq51074
  have eq51164 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38005 eq51067
    | (have r₁ := eq51067
       have r₂ := eq38005
       grind)
    | exact resolve eq51067 eq38005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38005 eq51067
  have eq51165 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq51164
  have eq51298 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51165 eq28
    | exact resolve eq28 eq51165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203788 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq51165 eq38027
    | exact resolve eq38027 eq51165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38027 eq51165
  have eq203948 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq203788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203788
  have eq391652 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203948 eq14355
    | exact resolve eq14355 eq203948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14355 eq203948
  have eq1096321 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40445 eq1250
    | exact resolve eq1250 eq40445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq40445
  have eq1165123 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1096321 eq39293
    | exact resolve eq39293 eq1096321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39293 eq1096321
  have eq1165231 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1165123
  have eq1165249 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1165231
       have r₂ := eq51298
       grind)
    | exact resolve eq1165231 eq51298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165231
  have eq1165613 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1165249 eq60
    | exact resolve eq60 eq1165249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165249
  have eq1166033 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1165613 eq391652
    | exact resolve eq391652 eq1165613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391652 eq1165613
  have eq1166229 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1166033
  have eq1166312 : x = (M.op x y) := by
    first
    | (have r₁ := eq1166229
       have r₂ := eq51298
       grind)
    | exact resolve eq1166229 eq51298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51298 eq1166229
  have eq1166350 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1166312 eq21
    | exact resolve eq21 eq1166312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167108 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1166350
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1166350
    | exact resolve eq1166350 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166350
  have eq1167506 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1167108 eq51149
    | exact resolve eq51149 eq1167108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51149
  have eq1167508 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1167108 eq51163
    | exact resolve eq51163 eq1167108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51163
  have eq1168365 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1167508
       have r₂ := eq28
       grind)
    | exact resolve eq1167508 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167508
  have eq1168367 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1167506
       have r₂ := eq28
       grind)
    | exact resolve eq1167506 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167506
  have eq1170243 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1168365 eq1168367
    | exact resolve eq1168367 eq1168365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168367
  have eq1170251 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1170243 eq28
    | exact resolve eq28 eq1170243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172530 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10186 eq12781
    | (have j0 := eq12781 (M.op x y) x
       have j1 := eq10186 (M.op x y) x
       grind)
    | exact resolve eq12781 eq10186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10186 eq12781
  have eq1173210 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq1172530
    | exact resolve eq1172530 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172530
  have eq1173816 : (M.op (σ x) (σ y)) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1168365 eq1173210
    | exact resolve eq1173210 eq1168365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173210
  have eq1174243 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq128 eq1173816
    | exact resolve eq1173816 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq1173816
  have eq1174485 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1170243 eq1174243
    | exact resolve eq1174243 eq1170243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170243 eq1174243
  have eq1174605 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq1174485
    | exact resolve eq1174485 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174485
  have eq1174676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1168365 eq1174605
    | exact resolve eq1174605 eq1168365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174605
  have eq1174727 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1174676
       have r₂ := eq28
       grind)
    | exact resolve eq1174676 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174676
  have eq1174764 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq1174727
    | exact resolve eq1174727 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174727
  have eq1174784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1168365 eq1174764
    | exact resolve eq1174764 eq1168365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174764
  have eq1174794 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1174784
       have r₂ := eq28
       grind)
    | exact resolve eq1174784 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174784
  have eq1174803 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq1174794
    | exact resolve eq1174794 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1174794
  have eq1174810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1168365 eq1174803
    | exact resolve eq1174803 eq1168365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168365 eq1174803
  have eq1174814 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1174810
       have r₂ := eq28
       grind)
    | exact resolve eq1174810 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1174810
  have eq1174835 : (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1174814 eq151
    | exact resolve eq151 eq1174814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq1174814
  have eq1174947 : (τ (σ y)) = (k x x) := by
    first
    | exact superpose eq1166312 eq1174835
    | exact resolve eq1174835 eq1166312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174835
  have eq1174970 : y = (k x x) := by
    first
    | exact superpose eq30 eq1174947
    | exact resolve eq1174947 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1174947
  have eq1174981 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1174970
       have i₂ := eq24285
       grind)
    | exact superpose eq24285 eq1174970
    | exact resolve eq1174970 eq24285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24285
  have eq1175038 : x ≠ y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3758 x
       have i₂ := eq1174970
       grind)
    | exact superpose eq1174970 eq3758
    | (have j0 := eq3758 x
       grind)
    | exact resolve eq3758 eq1174970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3758
  have eq1476951 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq60 x x
       have i₂ := eq1174981
       grind)
    | exact superpose eq1174981 eq60
    | exact resolve eq60 eq1174981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1174981
  have eq1477196 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1476951
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1476951
    | exact resolve eq1476951 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1476951
  have eq1477458 : x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq1166312 eq1477196
    | exact resolve eq1477196 eq1166312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166312 eq1477196
  have eq1477613 : x = (M.op x x) := by
    first
    | (have r₁ := eq1477458
       have r₂ := eq1175038
       grind)
    | exact resolve eq1477458 eq1175038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175038 eq1477458
  have eq1478098 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq224 x x
       have i₂ := eq1477613
       grind)
    | exact superpose eq1477613 eq224
    | exact resolve eq224 eq1477613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq1477613
  have eq1478241 : x = (k x x) := by grind
  clear eq1478098
  have eq1478330 : x = y := by
    first
    | (have i₁ := eq1478241
       have i₂ := eq1174970
       grind)
    | exact superpose eq1174970 eq1478241
    | exact resolve eq1478241 eq1174970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174970 eq1478241
  have eq1478925 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1478330
       grind)
    | exact superpose eq1478330 eq25
    | exact resolve eq25 eq1478330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1478330
  have eq1479521 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1478925
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1478925
    | exact resolve eq1478925 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1478925
  have eq1479676 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1167108 eq1479521
    | exact resolve eq1479521 eq1167108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167108 eq1479521
  have eq1479771 : False := by grind
  exact eq1479771

/-- `Equation2055`: `x = ((x ◇ y) ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_pyx_pxy_Equation2055 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2055 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2055.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X1 X2)) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 (M.op (M.op X0 X1) X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X0) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op X0 x) X0) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) X0) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X1) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq85 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq85
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
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
  have eq117 : ∀ X1 : G, (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq132 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq163 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq191 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq209 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq212 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) x)) X0) x) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) X0) (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq54 X0 X0
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) X2
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op (M.op X0 x) X0) = (M.op (M.op X0 (M.op (M.op X0 x) X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq245 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X0) = (M.op (M.op X0 (M.op (M.op X0 (σ x)) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq448 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq308 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq308
    | (have j0 := eq308 X0 x
       grind)
    | exact resolve eq308 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq308 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq308
    | (have j0 := eq308 X0 y
       grind)
    | exact resolve eq308 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq487 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op (M.op X0 (M.op X1 X2)) X0) X2
       have i₂ := eq14 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) X1 X3
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op X0 X1) X2 X3
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op x y) x)) = (M.op (M.op (M.op (M.op x y) x) (M.op x (M.op (M.op x y) x))) (M.op (M.op (M.op y X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x)))) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X0 X1) X0))) X2) = (M.op (M.op X2 (M.op (M.op X2 (M.op X0 (M.op (M.op X0 X1) X0))) X2)) (M.op (M.op (M.op X0 X1) X0) X5)) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq53 X2 (M.op X0 (M.op (M.op X0 X1) X0)) (M.op (M.op X1 x) x) X5
       have i₂ := eq53 X0 X1 x x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op x y) x)) X0)) (M.op x X2)) := by
    intro X0 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0)) (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op x y)) X0)) x) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq583 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq587 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 (M.op (M.op X0 X0) X0) x
       have i₂ := eq54 (M.op X0 (M.op (M.op X0 X0) X0)) x
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq695 : (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) x) := by
    first
    | (have i₁ := eq212 sF0
       have i₂ := eq54 sF0 x
       grind)
    | exact superpose eq54 eq212
    | exact resolve eq212 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq215 sF4
       have i₂ := eq54 sF4 sF2
       grind)
    | exact superpose eq54 eq215
    | exact resolve eq215 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq79 X0 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq783 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq771 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq771 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq771 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq771 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq793 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq783 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq783
    | (have j0 := eq783 X0 X1
       grind)
    | exact resolve eq783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq1032 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x)
       have i₂ := eq225 X0 x x
       grind)
    | exact superpose eq225 eq54
    | exact resolve eq54 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1032 X0
       have i₂ := eq225 X0 X0 X0
       grind)
    | exact superpose eq225 eq1032
    | exact resolve eq1032 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq3479 : (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)))) x) := by
    first
    | (have i₁ := eq582 (M.op (M.op sF0 sF0) sF0)
       have i₂ := eq1036 sF0
       grind)
    | exact superpose eq1036 eq582
    | exact resolve eq582 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3504 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq3479
       have i₂ := eq14 sF0 sF0 (M.op (M.op sF0 sF0) sF0)
       grind)
    | exact superpose eq14 eq3479
    | exact resolve eq3479 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479
  have eq3507 : (M.op (M.op (M.op x y) x) x) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq3504 eq582
    | exact resolve eq582 eq3504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq3554 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))))) (σ x)) := by
    first
    | (have i₁ := eq583 (M.op (M.op sF4 sF4) sF4)
       have i₂ := eq1036 sF4
       grind)
    | exact superpose eq1036 eq583
    | exact resolve eq583 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3579 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3554
       have i₂ := eq14 sF4 sF4 (M.op (M.op sF4 sF4) sF4)
       grind)
    | exact superpose eq14 eq3554
    | exact resolve eq3554 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq3597 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3579 eq583
    | exact resolve eq583 eq3579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq3683 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)))) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq695 eq240
    | exact resolve eq240 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq695
  have eq3714 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq3683 X0
       have i₂ := eq14 sF0 sF0 (M.op (M.op sF0 sF0) sF0)
       grind)
    | exact superpose eq14 eq3683
    | exact resolve eq3683 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683
  have eq3715 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq3714 x
       have i₂ := eq54 sF0 x
       grind)
    | exact superpose eq54 eq3714
    | exact resolve eq3714 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3714
  have eq3716 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3504 eq3715
    | exact resolve eq3715 eq3504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504 eq3715
  have eq3717 : (M.op (M.op (M.op x y) x) x) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq3716 eq3507
    | exact resolve eq3507 eq3716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq3756 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))))) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq720 eq245
    | exact resolve eq245 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq720
  have eq3787 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq3756 X0
       have i₂ := eq14 sF4 sF4 (M.op (M.op sF4 sF4) sF4)
       grind)
    | exact superpose eq14 eq3756
    | exact resolve eq3756 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756
  have eq3788 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3787 x
       have i₂ := eq54 sF4 x
       grind)
    | exact superpose eq54 eq3787
    | exact resolve eq3787 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3787
  have eq3789 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3579 eq3788
    | exact resolve eq3788 eq3579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579 eq3788
  have eq3790 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3789 eq3597
    | exact resolve eq3597 eq3789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4047 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq223 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4904 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq487 (M.op (M.op X0 X0) X0) (M.op X0 X1) x
       have i₂ := eq225 X0 X1 x
       grind)
    | exact superpose eq225 eq487
    | exact resolve eq487 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq4995 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4904 X0 X1
       have i₂ := eq14 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq14 eq4904
    | exact resolve eq4904 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4904
  have eq5005 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4995 X0 x
       have i₂ := eq54 X0 x
       grind)
    | exact superpose eq54 eq4995
    | exact resolve eq4995 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4995
  have eq5787 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq163 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq163
    | (have j0 := eq163 x
       grind)
    | exact resolve eq163 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq5806 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5787
  have eq5810 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5806
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5806
    | exact resolve eq5806 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5806
  have eq5827 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5810
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5810 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5810
  have eq5836 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5827 eq50
    | exact resolve eq50 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5864 : (k (k x x) x) = (τ (k (M.op (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq5836 eq448
    | exact resolve eq448 eq5836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq5867 : (k (k x x) x) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq5864
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq5864
    | exact resolve eq5864 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5864
  have eq5873 : (τ (M.op (σ x) (σ x))) = (k (k x x) x) := by
    first
    | (have i₁ := eq5867
       have i₂ := eq54 sF2 sF2
       grind)
    | exact superpose eq54 eq5867
    | exact resolve eq5867 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5867
  have eq5875 : (k x x) = (k (k x x) x) := by
    first
    | exact superpose eq5836 eq5873
    | exact resolve eq5873 eq5836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5873
  have eq6033 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq191 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq191
    | (have j0 := eq191 y
       grind)
    | exact resolve eq191 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq6049 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6033
  have eq6052 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6049
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq6049
    | exact resolve eq6049 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq6049
  have eq6076 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6052
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6052 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6052
  have eq6113 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6076 eq109
    | exact resolve eq109 eq6076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq6076
  have eq6142 : (k (k y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq6113 eq449
    | exact resolve eq449 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq6144 : (k (k y y) y) = (τ (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq6142
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq6142
    | exact resolve eq6142 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6142
  have eq6150 : (τ (M.op (σ y) (σ y))) = (k (k y y) y) := by
    first
    | (have i₁ := eq6144
       have i₂ := eq54 sF3 sF3
       grind)
    | exact superpose eq54 eq6144
    | exact resolve eq6144 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6144
  have eq6152 : (k y y) = (k (k y y) y) := by
    first
    | exact superpose eq6113 eq6150
    | exact resolve eq6150 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6150
  have eq6306 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq209
    | (have j0 := eq209 (M.op x y)
       grind)
    | exact resolve eq209 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq6321 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6306
  have eq6323 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq6321
    | exact resolve eq6321 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq6321
  have eq6354 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6323
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6323 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6323
  have eq6532 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq553 X0 X1 X2 X3
       have i₂ := eq5005 X0
       grind)
    | exact superpose eq5005 eq553
    | exact resolve eq553 eq5005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq6617 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6532 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x) X3 X4
       have i₂ := eq225 X0 x x
       grind)
    | exact superpose eq225 eq6532
    | exact resolve eq6532 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6532
  have eq6802 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) X0) (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6617 x X3 X4
       have i₂ := eq218 x x
       grind)
    | exact superpose eq218 eq6617
    | exact resolve eq6617 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq6617
  have eq6842 : ∀ X0 X3 X4 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6802 X0 X3 X4
       have i₂ := eq1036 X0
       grind)
    | exact superpose eq1036 eq6802
    | exact resolve eq6802 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6802
  have eq6857 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq6842 X0 X3 X4
       have i₂ := eq5005 X0
       grind)
    | exact superpose eq5005 eq6842
    | exact resolve eq6842 eq5005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6842
  have eq6917 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq6857 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq6857
    | (have j0 := eq6857 x y X0
       grind)
    | exact resolve eq6857 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6924 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq6857
    | (have j0 := eq6857 (σ x) (σ y) X0
       grind)
    | exact resolve eq6857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7189 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op x y) x)) X0) = (M.op (M.op X0 X0) (M.op x X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq571 x X2
       have i₂ := eq6857 x (M.op sF0 x) x
       grind)
    | exact superpose eq6857 eq571
    | exact resolve eq571 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq7210 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op x X1)) x) = X0 := by
    intro X0 X1
    first
    | exact superpose eq7189 eq212
    | exact resolve eq212 eq7189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq7189
  have eq7347 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq7210 X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7210
    | (have j0 := eq7210 X0 y
       grind)
    | exact resolve eq7210 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7210
  have eq7393 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq7347 (M.op (M.op X0 X0) X0)
       have i₂ := eq225 X0 X0 X0
       grind)
    | exact superpose eq225 eq7347
    | exact resolve eq7347 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7347
  have eq7472 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) X0) = (M.op (M.op X0 X0) (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq572 x X2
       have i₂ := eq6857 x (M.op sF4 sF2) x
       grind)
    | exact superpose eq6857 eq572
    | exact resolve eq572 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq7494 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) X1)) (σ x)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq7472 eq215
    | exact resolve eq215 eq7472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq7472
  have eq7633 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq7494
    | (have j0 := eq7494 X0 (σ y)
       grind)
    | exact resolve eq7494 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7494
  have eq7679 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7633 (M.op (M.op X0 X0) X0)
       have i₂ := eq225 X0 X0 X0
       grind)
    | exact superpose eq225 eq7633
    | exact resolve eq7633 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq7633
  have eq7758 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq587 X0
       have i₂ := eq5005 X0
       grind)
    | exact superpose eq5005 eq587
    | exact resolve eq587 eq5005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq5005
  have eq8013 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq223 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq7758 X0
       grind)
    | exact superpose eq7758 eq223
    | (have j0 := eq223 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq223 (M.op X0 X0) X0
       have r₂ := eq7758 X0
       grind)
    | exact resolve eq223 eq7758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7758
  have eq8020 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq8013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8013
  have eq8024 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8020 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq8020
    | exact resolve eq8020 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8020
  have eq8317 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) := by
    first
    | exact superpose eq3597 eq7393
    | exact resolve eq7393 eq3597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597
  have eq8322 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1036 X0
       have i₂ := eq7393 X0
       grind)
    | exact superpose eq7393 eq1036
    | exact resolve eq1036 eq7393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq8403 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op x y))) (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq7393 eq14
    | exact resolve eq14 eq7393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7393
  have eq8427 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8403 X1 X1
       have i₂ := eq14 X1 X1 sF0
       grind)
    | exact superpose eq14 eq8403
    | exact resolve eq8403 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8403
  have eq9214 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (σ x) (σ y)))) (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7679 eq14
    | exact resolve eq14 eq7679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7679
  have eq9238 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9214 X1 X1
       have i₂ := eq14 X1 X1 sF4
       grind)
    | exact superpose eq14 eq9214
    | exact resolve eq9214 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9214
  have eq12265 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op x y) x)) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op (M.op y X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq557 X0 X1 X2
       have i₂ := eq8427 (M.op sF0 x) (M.op sF0 x)
       grind)
    | exact superpose eq8427 eq557
    | exact resolve eq557 eq8427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq8427
  have eq12266 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op x y) x)) = (M.op (M.op (M.op (M.op x y) x) x) (M.op (M.op (M.op y X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3717 eq12265
    | exact resolve eq12265 eq3717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3717 eq12265
  have eq12267 : ∀ X0 X1 X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) (M.op (M.op (M.op y X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq6917 eq12266
    | exact resolve eq12266 eq6917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6917 eq12266
  have eq12452 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | (have i₁ := eq12267 (M.op (M.op x x) x) y x
       have i₂ := eq57 x y x
       grind)
    | exact superpose eq57 eq12267
    | exact resolve eq12267 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12267
  have eq12573 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9238 eq558
    | exact resolve eq558 eq9238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq9238
  have eq12574 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3790 eq12573
    | exact resolve eq12573 eq3790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790 eq12573
  have eq12575 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq8317 eq12574
    | exact resolve eq12574 eq8317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12574
  have eq12576 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq6924 eq12575
    | exact resolve eq12575 eq6924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6924 eq12575
  have eq12615 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (σ y)) := by
    first
    | (have i₁ := eq12576 (M.op (M.op x x) x) sF3 x
       have i₂ := eq57 x sF3 x
       grind)
    | exact superpose eq57 eq12576
    | exact resolve eq12576 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12576
  have eq14242 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) = (M.op (M.op X0 X0) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq493 X0 X1 X2 X3
       have i₂ := eq6857 X0 (M.op (M.op X1 X2) X1) X0
       grind)
    | exact superpose eq6857 eq493
    | exact resolve eq493 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq14526 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 X0 x
       have i₂ := eq14242 X0 X1 x X2
       grind)
    | exact superpose eq14242 eq57
    | exact resolve eq57 eq14242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14242
  have eq15006 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq3716 eq14526
    | exact resolve eq14526 eq3716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq15007 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq3789 eq14526
    | exact resolve eq14526 eq3789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789 eq14526
  have eq25751 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X0 X1) X0))) X2) = (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X1) X0) X5)) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq569 X0 X1 X2 X5
       have i₂ := eq6857 X2 (M.op X0 (M.op (M.op X0 X1) X0)) X2
       grind)
    | exact superpose eq6857 eq569
    | exact resolve eq569 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq25752 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X2 (M.op X0 X0)) X2) = (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X1) X0) X5)) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq25751 X0 X1 X2 X5
       have i₂ := eq6857 X0 X1 X0
       grind)
    | exact superpose eq6857 eq25751
    | exact resolve eq25751 eq6857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25751
  have eq25967 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25752 X0 (M.op (M.op x x) x) X1 x
       have i₂ := eq57 x X0 x
       grind)
    | exact superpose eq57 eq25752
    | exact resolve eq25752 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq25752
  have eq38101 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5827 eq92
    | exact resolve eq92 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq38112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq38112
    | exact resolve eq38112 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38112
  have eq38133 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq38122
       have r₂ := eq28
       grind)
    | exact resolve eq38122 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38122
  have eq38135 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq38133
    | exact resolve eq38133 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38133
  have eq38143 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq38135 eq6113
    | exact resolve eq6113 eq38135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq38148 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq38135 eq117
    | exact resolve eq117 eq38135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38135
  have eq38262 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq38148
       have r₂ := eq68
       grind)
    | exact resolve eq38148 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq38148
  have eq38266 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq38143
    | exact resolve eq38143 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq38143
  have eq38292 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq38262 eq97
    | exact resolve eq97 eq38262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq38262
  have eq38309 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq38292
  have eq42967 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6152
       have i₂ := eq38266
       grind)
    | exact superpose eq38266 eq6152
    | exact resolve eq6152 eq38266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6152
  have eq42972 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq38266
       grind)
    | exact superpose eq38266 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq38266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42990 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42972
  have eq43656 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq42967
       grind)
    | exact superpose eq42967 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq42967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42967
  have eq43665 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq43656
  have eq43679 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43665
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq43665
    | exact resolve eq43665 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43665
  have eq43696 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43679
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq43679
    | exact resolve eq43679 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43679
  have eq43697 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43696
  have eq43933 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15006 y y
       have i₂ := eq43697
       grind)
    | exact superpose eq43697 eq15006
    | exact resolve eq15006 eq43697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43697
  have eq43965 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12452 eq43933
    | exact resolve eq43933 eq12452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43933
  have eq45806 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq42990
       grind)
    | exact superpose eq42990 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq42990
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq42990
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq42990
       grind)
    | exact resolve eq13 eq42990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45845 : x ≠ y ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42990
  have eq45847 : y = (k y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq45806
  have eq45921 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38266
       have i₂ := eq45847
       grind)
    | exact superpose eq45847 eq38266
    | exact resolve eq38266 eq45847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38266 eq45847
  have eq45947 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq45921
  have eq45960 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq45947
       have r₂ := eq45845
       grind)
    | exact resolve eq45947 eq45845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45845 eq45947
  have eq46012 : y = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8024 y
       have i₂ := eq45960
       grind)
    | exact superpose eq45960 eq8024
    | exact resolve eq8024 eq45960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8024
  have eq46049 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15006 y y
       have i₂ := eq45960
       grind)
    | exact superpose eq45960 eq15006
    | exact resolve eq15006 eq45960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15006 eq45960
  have eq46082 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12452 eq46049
    | exact resolve eq46049 eq12452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12452 eq46049
  have eq46103 : y = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46012
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq46012
    | exact resolve eq46012 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46012
  have eq46385 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq46082
       grind)
    | exact superpose eq46082 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq46082
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq46082
       grind)
    | exact resolve eq13 eq46082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46082
  have eq46814 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46103 eq46
    | exact resolve eq46 eq46103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq46103
  have eq46847 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46814
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq46814
    | exact resolve eq46814 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46814
  have eq75967 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38101
       have i₂ := eq43965
       grind)
    | exact superpose eq43965 eq38101
    | exact resolve eq38101 eq43965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43965
  have eq76029 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq75967
  have eq76049 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq76029
    | exact resolve eq76029 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76029
  have eq76086 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76049 eq5836
    | exact resolve eq5836 eq76049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76049
  have eq76237 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq76086
    | exact resolve eq76086 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq76086
  have eq76245 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq76237
       have r₂ := eq46385
       grind)
    | exact resolve eq76237 eq46385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46385 eq76237
  have eq76252 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76245
       grind)
    | exact superpose eq76245 eq44
    | exact resolve eq44 eq76245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq76245
  have eq76307 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5827 eq76252
    | exact resolve eq76252 eq5827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5827 eq76252
  have eq76325 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq76307
    | exact resolve eq76307 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76307
  have eq76380 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76325 eq56
    | exact resolve eq56 eq76325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq76385 : (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76325 eq4047
    | exact resolve eq4047 eq76325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq78703 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76385 eq46847
    | exact resolve eq46847 eq76385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46847 eq76385
  have eq78714 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq78703
  have eq78721 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78714 eq76380
    | exact resolve eq76380 eq78714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76380 eq78714
  have eq78769 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq78721
  have eq78822 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78769 eq15007
    | exact resolve eq15007 eq78769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15007 eq78769
  have eq78863 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8317 eq78822
    | exact resolve eq78822 eq8317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8317 eq78822
  have eq78894 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12615 eq78863
    | exact resolve eq78863 eq12615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78863
  have eq79174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78894 eq76325
    | exact resolve eq76325 eq78894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76325 eq78894
  have eq79283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq79174
  have eq79324 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq79283
       have r₂ := eq28
       grind)
    | exact resolve eq79283 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79283
  have eq79416 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (M.op x y)) x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79324 eq12615
    | exact resolve eq12615 eq79324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12615 eq79324
  have eq79485 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8322 eq79416
    | exact resolve eq79416 eq8322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8322 eq79416
  have eq79515 : (τ (σ y)) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79485 eq5836
    | exact resolve eq5836 eq79485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5836
  have eq79605 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq79485 eq6857
    | exact resolve eq6857 eq79485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6857 eq79485
  have eq79676 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq79515
    | exact resolve eq79515 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq79515
  have eq79935 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5875
       have i₂ := eq79676
       grind)
    | exact superpose eq79676 eq5875
    | exact resolve eq5875 eq79676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5875
  have eq79942 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq79676
       grind)
    | exact superpose eq79676 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq79676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79676
  have eq79960 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq79942
  have eq83966 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79605 eq25967
    | exact resolve eq25967 eq79605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25967 eq79605
  have eq221393 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq54 x x
       have i₂ := eq79960
       grind)
    | exact superpose eq79960 eq54
    | exact resolve eq54 eq79960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79960
  have eq221502 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq221393
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq221393
    | exact resolve eq221393 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221393
  have eq221503 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq221502
  have eq221687 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq221503
       grind)
    | exact superpose eq221503 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq221503
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq221503
       grind)
    | exact resolve eq13 eq221503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221503
  have eq221753 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq221687
  have eq221937 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq793 x x
       have i₂ := eq221753
       grind)
    | exact superpose eq221753 eq793
    | (have j0 := eq793 x x
       grind)
    | exact resolve eq793 eq221753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq221753
  have eq221940 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq221937
  have eq221941 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq221940
  have eq221973 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq221941
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq221941
    | exact resolve eq221941 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221941
  have eq225763 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq221973 eq83966
    | exact resolve eq83966 eq221973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83966 eq221973
  have eq225963 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq225763
  have eq226076 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq225963
    | exact resolve eq225963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225963
  have eq229446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq226076 eq38309
    | exact resolve eq38309 eq226076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38309 eq226076
  have eq229681 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq229446
  have eq229744 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq229681
       have r₂ := eq28
       grind)
    | exact resolve eq229681 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229681
  have eq236626 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq223 y y
       have i₂ := eq229744
       grind)
    | exact superpose eq229744 eq223
    | exact resolve eq223 eq229744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq229744
  have eq236684 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq236626
  have eq236742 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq236684
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq236684
    | exact resolve eq236684 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236684
  have eq251089 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79935
       have i₂ := eq236742
       grind)
    | exact superpose eq236742 eq79935
    | exact resolve eq79935 eq236742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79935 eq236742
  have eq251119 : y = (M.op x y) := by grind
  clear eq251089
  have eq251668 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq251119 eq21
    | exact resolve eq21 eq251119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq251721 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq251119 eq221
    | exact resolve eq221 eq251119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq252025 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq251721
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq251721
    | exact resolve eq251721 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251721
  have eq252071 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq251668
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq251668
    | exact resolve eq251668 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251668
  have eq252081 : y = (M.op x x) := by
    first
    | exact superpose eq251119 eq252025
    | exact resolve eq252025 eq251119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252025
  have eq252161 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq252071 eq27
    | exact resolve eq27 eq252071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq253468 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq38101
       have i₂ := eq252081
       grind)
    | exact superpose eq252081 eq38101
    | exact resolve eq38101 eq252081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38101
  have eq253514 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq117 x
       have i₂ := eq252081
       grind)
    | exact superpose eq252081 eq117
    | exact resolve eq117 eq252081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq252081
  have eq253719 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq253514
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq253514
    | exact resolve eq253514 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq253514
  have eq253739 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq253468
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq253468
    | exact resolve eq253468 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253468
  have eq253780 : y = (k y x) := by
    first
    | exact superpose eq251119 eq253719
    | exact resolve eq253719 eq251119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251119 eq253719
  have eq253786 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq252071 eq253739
    | exact resolve eq253739 eq252071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253739
  have eq253952 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq253780
       grind)
    | exact superpose eq253780 eq76
    | exact resolve eq76 eq253780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq253780
  have eq254022 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq252071 eq253952
    | exact resolve eq253952 eq252071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253952
  have eq254044 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq254022
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq254022
    | exact resolve eq254022 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254022
  have eq254066 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq252071 eq254044
    | exact resolve eq254044 eq252071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254044
  have eq280424 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq253786 eq54
    | exact resolve eq54 eq253786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq253786
  have eq280508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq252161 eq280424
    | exact resolve eq280424 eq252161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280424
  have eq280580 : x = y := by
    first
    | (have r₁ := eq280508
       have r₂ := eq28
       grind)
    | exact resolve eq280508 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280508
  have eq280620 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq280580
       grind)
    | exact superpose eq280580 eq25
    | exact resolve eq25 eq280580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq280642 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq280580
       grind)
    | exact superpose eq280580 eq133
    | exact resolve eq133 eq280580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq280580
  have eq281219 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq252071 eq280642
    | exact resolve eq280642 eq252071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280642
  have eq281241 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq252071 eq280620
    | exact resolve eq280620 eq252071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252071 eq280620
  have eq281471 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq6354 eq281219
    | exact resolve eq281219 eq6354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6354 eq281219
  have eq281493 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq281241
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq281241
    | exact resolve eq281241 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq281241
  have eq281631 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq132 eq281471
    | exact resolve eq281471 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq281471
  have eq281741 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq254066 eq281631
    | exact resolve eq281631 eq254066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254066 eq281631
  have eq282506 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq281493 eq252161
    | exact resolve eq252161 eq281493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252161 eq281493
  have eq283588 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq281741 eq282506
    | exact resolve eq282506 eq281741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281741 eq282506
  have eq283589 : False := by grind
  exact eq283589

/-- `Equation2062`: `x = ((x ◇ y) ◇ y) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_pyy_pxy_y_pyx_Equation2062 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2062 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2062.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq174 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op x X0)) := by
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
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op (M.op X0 X1) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X1) (M.op X0 X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 X1) X2
       have i₂ := eq16 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X1) X2 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) ≠ X0 ∨ (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) = (k (M.op X0 X1) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op (M.op X0 X2) X2)
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 X1) (M.op (M.op X0 X2) X2)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op (M.op (M.op x y) y) X0) X0) x) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op x (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq394 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ x))) = (σ (k X0 (k x x))) := by
    intro X0
    first
    | exact superpose eq97 eq38
    | exact resolve eq38 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq97
  have eq441 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq357 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq357
    | exact resolve eq357 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq585 : ∀ X0 : G, (M.op (M.op (k X0 X0) X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq184 X0 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq184
    | exact resolve eq184 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq206 eq178
    | exact resolve eq178 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq213 eq179
    | exact resolve eq179 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq174 eq188
    | exact resolve eq188 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq658 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq186 eq188
    | exact resolve eq188 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq673 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) := by
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
  have eq675 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq675
       have i₂ := eq183 sF2
       grind)
    | exact superpose eq183 eq675
    | exact resolve eq675 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq682 : (M.op x y) ≠ (k x x) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq673
       have i₂ := eq183 x
       grind)
    | exact superpose eq183 eq673
    | exact resolve eq673 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq703 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq705 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) X0) (M.op X1 X2)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 X1 : G, (k X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq758 X0 X1
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq758
    | (have j0 := eq758 X0 X1
       grind)
    | (have r₁ := eq758 X0 X0
       have r₂ := eq183 X0
       grind)
    | exact resolve eq758 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq809 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) X0) (M.op X1 X2)) = X1 ∨ (M.op X1 X0) = (k X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq710 X0 X1 X2
       have i₂ := eq183 X1
       grind)
    | exact superpose eq183 eq710
    | (have j0 := eq710 X0 X1 X2
       grind)
    | exact resolve eq710 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq813 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq705
       have i₂ := eq183 sF2
       grind)
    | exact superpose eq183 eq705
    | exact resolve eq705 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq815 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq703
       have i₂ := eq183 x
       grind)
    | exact superpose eq183 eq703
    | exact resolve eq703 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq831 : ∀ X0 X1 : G, (k X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq761 X0 X1
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq761
    | (have j0 := eq761 X0 X1
       grind)
    | exact resolve eq761 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq874 : (M.op x (M.op x y)) = (M.op x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq658 eq206
    | exact resolve eq206 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq957 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq175 eq198
    | exact resolve eq198 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq959 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq194 eq198
    | exact resolve eq198 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq198
  have eq982 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq959 eq213
    | exact resolve eq213 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1710 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op x (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq177 x X0 x
       have i₂ := eq656 X0
       grind)
    | exact superpose eq656 eq177
    | exact resolve eq177 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq1711 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq957 eq177
    | exact resolve eq177 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1718 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op X0 (M.op X0 X1)) X2) X3
       have i₂ := eq177 X0 X1 X2
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1736 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq982 eq1711
    | exact resolve eq1711 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711
  have eq1737 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq874 eq1710
    | exact resolve eq1710 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq2654 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq815
       grind)
    | exact superpose eq815 eq39
    | exact resolve eq39 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq2655 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2654
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2654
    | exact resolve eq2654 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654
  have eq2657 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq2655
    | exact resolve eq2655 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq2667 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) X0)) = (M.op (M.op x (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq635 eq177
    | exact resolve eq177 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2677 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq658 eq2667
    | exact resolve eq2667 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq2697 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq642 eq177
    | exact resolve eq177 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2707 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq959 eq2697
    | exact resolve eq2697 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq6994 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 X1 (M.op X0 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6997 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op (M.op x (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq178 eq180
    | exact resolve eq180 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq6999 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq179 eq180
    | exact resolve eq180 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq7003 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq180 (M.op X0 X0) X0 X0
       have i₂ := eq180 X0 X0 X0
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq7019 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7003 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq7003
    | exact resolve eq7003 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7003
  have eq7021 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq959 eq6999
    | exact resolve eq6999 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq6999
  have eq7022 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq658 eq6997
    | exact resolve eq6997 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq6997
  have eq7030 : ∀ X0 : G, (M.op (M.op (k X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7019 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq7019
    | exact resolve eq7019 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7019
  have eq7220 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq7021 sF2
       have i₂ := eq183 sF2
       grind)
    | exact superpose eq183 eq7021
    | exact resolve eq7021 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7255 : (M.op (M.op x y) y) = (M.op (k x x) x) := by
    first
    | (have i₁ := eq7022 x
       have i₂ := eq183 x
       grind)
    | exact superpose eq183 eq7022
    | exact resolve eq7022 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7292 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 X0) X0 X1
       have i₂ := eq7030 X0
       grind)
    | exact superpose eq7030 eq16
    | exact resolve eq16 eq7030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7298 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (k X0 X0) X0) (M.op (M.op (k X0 X0) X0) X1)) (M.op (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op (k X0 X0) X0) X0 X2 x
       have i₂ := eq7030 X0
       grind)
    | exact superpose eq7030 eq176
    | exact resolve eq176 eq7030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7307 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (M.op (k X0 X0) X0) (M.op (M.op (k X0 X0) X0) X1)) (M.op (k X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7298 X0 X1 X2
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq7298
    | exact resolve eq7298 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7298
  have eq7318 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq7220 eq7030
    | exact resolve eq7030 eq7220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7371 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq7030 x
       have i₂ := eq7255
       grind)
    | exact superpose eq7255 eq7030
    | exact resolve eq7030 eq7255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7426 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq7220 eq7292
    | exact resolve eq7292 eq7220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7427 : (k x x) = (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq7292 x x
       have i₂ := eq7255
       grind)
    | exact superpose eq7255 eq7292
    | exact resolve eq7292 eq7255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7255
  have eq7474 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7426 eq982
    | exact resolve eq982 eq7426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq7426
  have eq7510 : (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | exact superpose eq7474 eq1736
    | exact resolve eq1736 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7533 : (k x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq7427 eq874
    | exact resolve eq874 eq7427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq7427
  have eq7567 : (M.op (M.op x y) y) = (M.op (k x x) (M.op x y)) := by
    first
    | exact superpose eq7533 eq7022
    | exact resolve eq7022 eq7533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7569 : (k x x) = (M.op x (k x x)) := by
    first
    | exact superpose eq7533 eq1737
    | exact resolve eq1737 eq7533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq7614 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq7510 eq7021
    | exact resolve eq7021 eq7510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7021 eq7510
  have eq7636 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq7614
       have i₂ := eq183 (k sF2 sF2)
       grind)
    | exact superpose eq183 eq7614
    | exact resolve eq7614 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7614
  have eq7709 : (M.op (M.op x y) y) = (M.op (k x x) (k x x)) := by
    first
    | (have i₁ := eq7022 (k x x)
       have i₂ := eq7569
       grind)
    | exact superpose eq7569 eq7022
    | exact resolve eq7022 eq7569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7022 eq7569
  have eq7731 : (M.op (M.op x y) y) = (k (k x x) (k x x)) := by
    first
    | (have i₁ := eq7709
       have i₂ := eq183 (k x x)
       grind)
    | exact superpose eq183 eq7709
    | exact resolve eq7709 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7709
  have eq9473 : (k (σ (k x x)) (k (σ x) (σ x))) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq394 (k x x)
       have i₂ := eq7731
       grind)
    | exact superpose eq7731 eq394
    | exact resolve eq394 eq7731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq7731
  have eq9483 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq9473
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq9473
    | exact resolve eq9473 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9473
  have eq9486 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq9483
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9483
    | exact resolve eq9483 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9483
  have eq9488 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq7636 eq9486
    | exact resolve eq9486 eq7636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7636 eq9486
  have eq9493 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq9488 eq15
    | exact resolve eq15 eq9488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9695 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X1) X3)) = (M.op (M.op (M.op X0 (M.op X0 X2)) (M.op (M.op X0 (M.op X0 X2)) X4)) (M.op X0 (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6994 (M.op X0 (M.op X0 X2)) (M.op (M.op (M.op X0 X1) X1) X3) X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq6994
    | exact resolve eq6994 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq9697 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op (k X0 X0) X0) (M.op (M.op (k X0 X0) X0) X2)) (M.op (k X0 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6994 (M.op (k X0 X0) X0) (M.op X0 X1) X2
       have i₂ := eq185 X0 X1
       grind)
    | exact superpose eq185 eq6994
    | exact resolve eq6994 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq9751 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X0) X1) X1) = (M.op (M.op (M.op (k X0 X0) X0) X0) (M.op (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6994 (M.op (k X0 X0) X0) X1 (k X0 X0)
       have i₂ := eq585 X0
       grind)
    | exact superpose eq585 eq6994
    | exact resolve eq6994 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq9822 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6994 X0 X1 x
       have i₂ := eq6994 X0 X2 x
       grind)
    | exact superpose eq6994 eq6994
    | exact resolve eq6994 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9920 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (k X0 X0) X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9751 X0 X1
       have i₂ := eq16 (k X0 X0) X0 X0
       grind)
    | exact superpose eq16 eq9751
    | exact resolve eq9751 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9751
  have eq9957 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9697 X0 X1 x
       have i₂ := eq7307 X0 x X0
       grind)
    | exact superpose eq7307 eq9697
    | exact resolve eq9697 eq7307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7307 eq9697
  have eq9958 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op X0 X1) X1) X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9695 X0 X1 x X3 x
       have i₂ := eq1718 X0 x x (M.op X0 x)
       grind)
    | exact superpose eq1718 eq9695
    | exact resolve eq9695 eq1718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718 eq9695
  have eq9978 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9958 X0 X1 x
       have i₂ := eq9957 (M.op (M.op X0 X1) X1) x
       grind)
    | exact superpose eq9957 eq9958
    | exact resolve eq9958 eq9957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9958
  have eq9988 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9957 X0 (M.op X0 x)
       have i₂ := eq9957 X0 x
       grind)
    | exact superpose eq9957 eq9957
    | exact resolve eq9957 eq9957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10008 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9957 (M.op (M.op X0 X1) X1) (k X0 X0)
       have i₂ := eq184 X0 X1
       grind)
    | exact superpose eq184 eq9957
    | exact resolve eq9957 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq10080 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6994 X0 X1 x
       have i₂ := eq9957 X0 x
       grind)
    | exact superpose eq9957 eq6994
    | exact resolve eq6994 eq9957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10195 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10008 X0 X1
       have i₂ := eq9978 X0 X1
       grind)
    | exact superpose eq9978 eq10008
    | exact resolve eq10008 eq9978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10008
  have eq11045 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9988 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq9988
    | exact resolve eq9988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11046 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9988 (τ X0)
       have i₂ := eq441 X0 X0
       grind)
    | exact superpose eq441 eq9988
    | exact resolve eq9988 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq11067 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X0 X0)) = (M.op (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6994 X0 (k X0 X0) X1
       have i₂ := eq9988 X0
       grind)
    | exact superpose eq9988 eq6994
    | exact resolve eq6994 eq9988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9988
  have eq11117 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11067 X0 x
       have i₂ := eq9957 X0 x
       grind)
    | exact superpose eq9957 eq11067
    | exact resolve eq11067 eq9957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11067
  have eq11129 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11117 X0
       have i₂ := eq183 (k X0 X0)
       grind)
    | exact superpose eq183 eq11117
    | exact resolve eq11117 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11117
  have eq11657 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op x y)) X0)) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq635 eq9822
    | exact resolve eq9822 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq11672 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq642 eq9822
    | exact resolve eq9822 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq11738 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9822 (M.op (M.op X0 X1) X1) X2 X0
       have i₂ := eq10195 X0 X1
       grind)
    | exact superpose eq10195 eq9822
    | exact resolve eq9822 eq10195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11746 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op (M.op X0 (M.op X0 X1)) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9822 (M.op X0 X2) X3 X2
       have i₂ := eq6994 X0 X2 X1
       grind)
    | exact superpose eq6994 eq9822
    | exact resolve eq9822 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11915 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7030 X0
       have i₂ := eq9822 (k X0 X0) X0 X1
       grind)
    | (have i₁ := eq7030 X0
       have i₂ := eq9822 (k X0 X0) X1 X0
       grind)
    | exact superpose eq9822 eq7030
    | exact resolve eq7030 eq9822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7030
  have eq12101 : ∀ X0 X2 X3 : G, (M.op (M.op (k X0 X0) X0) X2) = (M.op (M.op (M.op X0 X2) X3) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq11746 X0 x X2 X3
       have i₂ := eq9957 X0 x
       grind)
    | exact superpose eq9957 eq11746
    | exact resolve eq11746 eq9957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11746
  have eq12150 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) X1) := by
    intro X1
    first
    | exact superpose eq2707 eq11672
    | exact resolve eq11672 eq2707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707 eq11672
  have eq12164 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) y) X1) X1) := by
    intro X1
    first
    | exact superpose eq2677 eq11657
    | exact resolve eq11657 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677 eq11657
  have eq12259 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq12150 x
       have i₂ := eq12101 sF4 sF3 x
       grind)
    | exact superpose eq12101 eq12150
    | exact resolve eq12150 eq12101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12150
  have eq12268 : (M.op x (M.op x y)) = (M.op (M.op (k (M.op x y) (M.op x y)) (M.op x y)) y) := by
    first
    | (have i₁ := eq12164 x
       have i₂ := eq12101 sF0 y x
       grind)
    | exact superpose eq12101 eq12164
    | exact resolve eq12164 eq12101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12101 eq12164
  have eq12301 : (k (σ x) (σ x)) = (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq7474 eq12259
    | exact resolve eq12259 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12259
  have eq12304 : (k x x) = (M.op (M.op (k (M.op x y) (M.op x y)) (M.op x y)) y) := by
    first
    | exact superpose eq7533 eq12268
    | exact resolve eq12268 eq7533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7533 eq12268
  have eq12322 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11915 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq11915
    | exact resolve eq11915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12362 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X1) = (M.op (M.op (M.op (M.op (k X0 X0) X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (k X0 X0) X1) X2 X1
       have i₂ := eq11915 X0 X1
       grind)
    | exact superpose eq11915 eq16
    | exact resolve eq16 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12376 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (k X0 X0) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9822 (M.op (k X0 X0) X1) X2 X1
       have i₂ := eq11915 X0 X1
       grind)
    | exact superpose eq11915 eq9822
    | exact resolve eq9822 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12378 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (M.op X0 X1) (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10195 (M.op (k X0 X0) X1) X1
       have i₂ := eq11915 X0 X1
       grind)
    | exact superpose eq11915 eq10195
    | exact resolve eq10195 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12387 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12362 X0 X1 x
       have i₂ := eq12376 X0 X1 x
       grind)
    | exact superpose eq12376 eq12362
    | exact resolve eq12362 eq12376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12362
  have eq13705 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7292 X0 X0
       have i₂ := eq10080 X0 X1
       grind)
    | exact superpose eq10080 eq7292
    | exact resolve eq7292 eq10080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13890 : ∀ X0 : G, (M.op (k (σ x) (σ x)) (σ y)) = (M.op (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) X0) X0) := by
    intro X0
    first
    | exact superpose eq12301 eq9822
    | exact resolve eq9822 eq12301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12301
  have eq13898 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq13890 x
       have i₂ := eq9920 sF4 x
       grind)
    | exact superpose eq9920 eq13890
    | exact resolve eq13890 eq9920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13890
  have eq13930 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq13898 eq11915
    | exact resolve eq11915 eq13898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13898
  have eq13988 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13930 eq7292
    | exact resolve eq7292 eq13930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14010 : (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq13930 eq9957
    | exact resolve eq9957 eq13930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13930
  have eq14013 : (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq14010
       have i₂ := eq11129 sF4
       grind)
    | exact superpose eq11129 eq14010
    | exact resolve eq14010 eq11129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14010
  have eq14283 : ∀ X0 : G, (M.op (k x x) y) = (M.op (M.op (M.op (k (M.op x y) (M.op x y)) (M.op x y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq12304 eq9822
    | exact resolve eq9822 eq12304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14291 : (k (M.op x y) (M.op x y)) = (M.op (k x x) y) := by
    first
    | (have i₁ := eq14283 x
       have i₂ := eq9920 sF0 x
       grind)
    | exact superpose eq9920 eq14283
    | exact resolve eq14283 eq9920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9920 eq14283
  have eq14323 : x = (M.op (k (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq11915 x y
       have i₂ := eq14291
       grind)
    | exact superpose eq14291 eq11915
    | exact resolve eq11915 eq14291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14291
  have eq14381 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq14323 eq7292
    | exact resolve eq7292 eq14323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7292
  have eq14668 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (k X0 X0) X2) X2)) ∨ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (k X0 X0) X2) X2)) = (k (M.op (M.op X0 X1) X1) (M.op (M.op (k X0 X0) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 (k X0 X0) X0 X2
       have i₂ := eq10080 X0 X1
       grind)
    | exact superpose eq10080 eq182
    | exact resolve eq182 eq10080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq15020 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ (M.op (M.op (M.op X0 X1) X1) X0) ∨ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (k X0 X0) X2) X2)) = (k (M.op (M.op X0 X1) X1) (M.op (M.op (k X0 X0) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14668 X0 X1 X2
       have i₂ := eq11915 X0 X2
       grind)
    | exact superpose eq11915 eq14668
    | (have j0 := eq14668 X0 X1 X2
       grind)
    | exact resolve eq14668 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14668
  have eq15209 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (k X0 X0) X2) X2)) = (k (M.op (M.op X0 X1) X1) (M.op (M.op (k X0 X0) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15020 X0 X1 X2
       have i₂ := eq10195 X0 X1
       grind)
    | exact superpose eq10195 eq15020
    | (have j0 := eq15020 X0 X1 X2
       grind)
    | exact resolve eq15020 eq10195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15020
  have eq15339 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = (k (M.op (M.op X0 X1) X1) X0) ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15209 X0 X1 X1
       have i₂ := eq11915 X0 X1
       grind)
    | exact superpose eq11915 eq15209
    | (have j0 := eq15209 X0 X1 x
       grind)
    | exact resolve eq15209 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15209
  have eq15465 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15339 X0 X1
       have i₂ := eq10195 X0 X1
       grind)
    | exact superpose eq10195 eq15339
    | (have j0 := eq15339 X0 X1
       grind)
    | exact resolve eq15339 eq10195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15339
  have eq16537 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9957 (M.op X0 X1) X0
       have i₂ := eq12387 X0 X1
       grind)
    | exact superpose eq12387 eq9957
    | exact resolve eq9957 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16539 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11915 X0 X1
       have i₂ := eq12387 X0 X1
       grind)
    | exact superpose eq12387 eq11915
    | exact resolve eq11915 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16565 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X2) X2) = (M.op (M.op (k X0 X0) (M.op (M.op X0 X1) X0)) (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6994 (k X0 X0) X2 X1
       have i₂ := eq12387 X0 X1
       grind)
    | exact superpose eq12387 eq6994
    | exact resolve eq6994 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6994
  have eq16579 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X2) X2) = (M.op (k (k X0 X0) (k X0 X0)) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16565 X0 X1 X2
       have i₂ := eq12387 (k X0 X0) (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq12387 eq16565
    | exact resolve eq16565 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16565
  have eq16592 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16537 X0 X1
       have i₂ := eq12378 X0 X1
       grind)
    | exact superpose eq12378 eq16537
    | exact resolve eq16537 eq12378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12378 eq16537
  have eq16693 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X2) X2) = (M.op (M.op (k X0 X0) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16579 X0 X1 X2
       have i₂ := eq11129 X0
       grind)
    | exact superpose eq11129 eq16579
    | exact resolve eq16579 eq11129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11129 eq16579
  have eq16748 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X0) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16693 X0 X1 x
       have i₂ := eq11915 X0 x
       grind)
    | exact superpose eq11915 eq16693
    | exact resolve eq16693 eq11915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16693
  have eq16958 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9822 (M.op (M.op X0 X1) X0) X2 X1
       have i₂ := eq16539 X0 X1
       grind)
    | exact superpose eq16539 eq9822
    | exact resolve eq9822 eq16539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16962 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10195 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq16539 X0 X1
       grind)
    | exact superpose eq16539 eq10195
    | exact resolve eq10195 eq16539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16963 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16962 X0 X1
       have i₂ := eq9957 (M.op X0 X1) X0
       grind)
    | exact superpose eq9957 eq16962
    | exact resolve eq16962 eq9957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16962
  have eq17413 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op (M.op (M.op X0 X1) X1) X0) ∨ (k (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) X1) X0
       have i₂ := eq13705 X0 X1
       grind)
    | exact superpose eq13705 eq12
    | (have j0 := eq12 (M.op (M.op X0 X1) X1) X0
       grind)
    | exact resolve eq12 eq13705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13705
  have eq17521 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op X0 X1) X1) X0) ∨ (k (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17413 X0 X1
       grind)
    | (have r₁ := eq17413 X0 X1
       have r₂ := eq183 X0
       grind)
    | exact resolve eq17413 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17413
  have eq17640 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17521 X0 X1
       have i₂ := eq10195 X0 X1
       grind)
    | exact superpose eq10195 eq17521
    | (have j0 := eq17521 X0 X1
       grind)
    | exact resolve eq17521 eq10195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10195 eq17521
  have eq17669 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17640 X0 X1
       have j1 := eq15465 X0 X1
       grind)
    | (have r₁ := eq17640 X0 X1
       have r₂ := eq15465 X0 X1
       grind)
    | exact resolve eq17640 eq15465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15465 eq17640
  have eq30347 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X1) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11045 (M.op (M.op X0 X1) X1)
       have i₂ := eq9978 X0 X1
       grind)
    | exact superpose eq9978 eq11045
    | exact resolve eq11045 eq9978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11045
  have eq30348 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X1) X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11046 (M.op (M.op X0 X1) X1)
       have i₂ := eq9978 X0 X1
       grind)
    | exact superpose eq9978 eq11046
    | exact resolve eq11046 eq9978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11046
  have eq30350 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X2) X2) = (σ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12322 (M.op (M.op X0 X1) X1) X2
       have i₂ := eq9978 X0 X1
       grind)
    | exact superpose eq9978 eq12322
    | exact resolve eq12322 eq9978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12322
  have eq30943 : ∀ X0 : G, (σ y) = (M.op (σ (M.op (M.op y X0) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq30347 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30347
    | (have j0 := eq30347 y X0
       grind)
    | exact resolve eq30347 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31021 : (σ y) = (M.op (σ (M.op (k y y) y)) (σ y)) := by
    first
    | (have i₁ := eq30943 x
       have i₂ := eq10080 y x
       grind)
    | exact superpose eq10080 eq30943
    | exact resolve eq30943 eq10080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30943
  have eq31722 : (σ (M.op (k y y) y)) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq31021 eq9978
    | exact resolve eq9978 eq31021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31021
  have eq31735 : (M.op (k (σ y) (σ y)) (σ y)) = (σ (M.op (k y y) y)) := by
    first
    | (have i₁ := eq31722
       have i₂ := eq16592 sF3 sF3
       grind)
    | exact superpose eq16592 eq31722
    | exact resolve eq31722 eq16592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31722
  have eq32460 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op (M.op (σ (M.op x y)) X0) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28 eq30348
    | exact resolve eq30348 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30348
  have eq32544 : (M.op x y) = (M.op (τ (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) (M.op x y)) := by
    first
    | (have i₁ := eq32460 x
       have i₂ := eq10080 sF1 x
       grind)
    | exact superpose eq10080 eq32460
    | exact resolve eq32460 eq10080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32460
  have eq33240 : (τ (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq32544 eq9978
    | exact resolve eq9978 eq32544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32544
  have eq33255 : (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = (τ (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq33240
       have i₂ := eq16592 sF0 sF0
       grind)
    | exact superpose eq16592 eq33240
    | exact resolve eq33240 eq16592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33240
  have eq53162 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k (M.op (M.op X0 X0) X2) (M.op (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9978 (M.op (M.op (M.op X0 X1) X1) X2) X2
       have i₂ := eq11738 X0 X1 X2
       grind)
    | exact superpose eq11738 eq9978
    | exact resolve eq9978 eq11738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9978 eq11738
  have eq53191 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53162 X0 X1 X2
       have i₂ := eq16592 (M.op X0 X0) X2
       grind)
    | exact superpose eq16592 eq53162
    | exact resolve eq53162 eq16592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53162
  have eq53611 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (k X0 X0) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53191 X0 X1 X2
       have i₂ := eq16592 X0 X0
       grind)
    | exact superpose eq16592 eq53191
    | exact resolve eq53191 eq16592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53191
  have eq55381 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (k X0 X0) X1) X2) = (M.op (M.op (M.op (M.op (M.op (k X0 X0) X1) X2) X3) X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op (k X0 X0) X1) X2) X3 X2
       have i₂ := eq12376 X0 X1 X2
       grind)
    | exact superpose eq12376 eq16
    | exact resolve eq16 eq12376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55402 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op (k X0 X0) X1) X2) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9822 (M.op (M.op (k X0 X0) X1) X2) X3 X2
       have i₂ := eq12376 X0 X1 X2
       grind)
    | exact superpose eq12376 eq9822
    | exact resolve eq9822 eq12376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55453 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) X2) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55381 X0 X1 X2 x
       have i₂ := eq55402 X0 X1 X2 x
       grind)
    | exact superpose eq55402 eq55381
    | exact resolve eq55381 eq55402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55381 eq55402
  have eq61224 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16592 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq16539 X0 X1
       grind)
    | exact superpose eq16539 eq16592
    | exact resolve eq16592 eq16539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16592
  have eq61706 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X0) X1) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61224 X0 X1
       have i₂ := eq12387 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact superpose eq12387 eq61224
    | exact resolve eq61224 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61224
  have eq61891 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (k (M.op X0 X1) (M.op X0 X1)) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61706 X0 X1
       have i₂ := eq55453 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq55453 eq61706
    | exact resolve eq61706 eq55453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61706
  have eq62033 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61891 X0 X1
       have i₂ := eq12387 (M.op X0 X1) X0
       grind)
    | exact superpose eq12387 eq61891
    | exact resolve eq61891 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61891
  have eq62113 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (k X0 X0) X1) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62033 X0 X1
       have i₂ := eq55453 X0 X1 X0
       grind)
    | exact superpose eq55453 eq62033
    | exact resolve eq62033 eq55453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55453 eq62033
  have eq62201 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq14013 eq16748
    | exact resolve eq16748 eq14013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16748
  have eq62852 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq62201 x
       have i₂ := eq12387 sF4 x
       grind)
    | exact superpose eq12387 eq62201
    | exact resolve eq62201 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12387 eq62201
  have eq65450 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (M.op (σ (M.op (M.op (k X0 X0) X1) X2)) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30350 (M.op (M.op (k X0 X0) X1) X2) X2 X3
       have i₂ := eq12376 X0 X1 X2
       grind)
    | exact superpose eq12376 eq30350
    | exact resolve eq30350 eq12376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12376
  have eq75770 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16958 X0 X1 X0
       have i₂ := eq9822 (M.op X0 X1) X0 X2
       grind)
    | (have i₁ := eq16958 X0 X1 X0
       have i₂ := eq9822 (M.op X0 X1) X2 X0
       grind)
    | exact superpose eq9822 eq16958
    | exact resolve eq16958 eq9822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9822 eq16958
  have eq83947 : ∀ X0 X1 X2 : G, (σ (M.op (k X0 X0) X1)) = (M.op (M.op (σ (M.op (M.op (k X0 X0) X1) X0)) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30350 (M.op (M.op (k X0 X0) X1) X0) X1 X2
       have i₂ := eq62113 X0 X1
       grind)
    | exact superpose eq62113 eq30350
    | exact resolve eq30350 eq62113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30350 eq62113
  have eq83958 : ∀ X0 X1 : G, (σ (M.op (k X0 X0) X1)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83947 X0 X1 x
       have i₂ := eq65450 X0 X1 X0 x
       grind)
    | exact superpose eq65450 eq83947
    | exact resolve eq83947 eq65450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65450 eq83947
  have eq184483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2657 eq813
    | exact resolve eq813 eq2657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184498 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq184483
       have r₂ := eq27
       grind)
    | exact resolve eq184483 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184483
  have eq185134 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq184498 eq680
    | (have r₁ := eq680
       have r₂ := eq184498
       grind)
    | exact resolve eq680 eq184498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq184498
  have eq185270 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq185134
  have eq185271 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq185270
  have eq185357 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2657 eq185271
    | exact resolve eq185271 eq2657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185271
  have eq185433 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq185357 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq185357
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq185357
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq185357
       grind)
    | exact resolve eq13 eq185357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185357
  have eq185599 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq185433
       have r₂ := eq26
       grind)
    | exact resolve eq185433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185433
  have eq185647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2657 eq185599
    | exact resolve eq185599 eq2657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2657 eq185599
  have eq185677 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq185647
       have r₂ := eq27
       grind)
    | exact resolve eq185647 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185647
  have eq185706 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq682
       have i₂ := eq185677
       grind)
    | exact superpose eq185677 eq682
    | (have r₁ := eq682
       have r₂ := eq185677
       grind)
    | exact resolve eq682 eq185677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq185758 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq185677
       grind)
    | exact superpose eq185677 eq39
    | exact resolve eq39 eq185677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185677
  have eq185834 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq185706
  have eq185835 : (M.op x y) = (M.op y x) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq185834
  have eq185893 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq185758
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq185758
    | exact resolve eq185758 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185758
  have eq185952 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq185893
    | exact resolve eq185893 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185893
  have eq186030 : (k y y) = (M.op y (M.op x y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9957 y x
       have i₂ := eq185835
       grind)
    | exact superpose eq185835 eq9957
    | exact resolve eq9957 eq185835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9957
  have eq186043 : y = (M.op (M.op (M.op x y) y) x) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16539 y x
       have i₂ := eq185835
       grind)
    | exact superpose eq185835 eq16539
    | exact resolve eq16539 eq185835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186052 : (σ y) = (M.op (σ (M.op (M.op x y) x)) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30347 y x
       have i₂ := eq185835
       grind)
    | exact superpose eq185835 eq30347
    | exact resolve eq30347 eq185835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185835
  have eq186124 : (σ y) = (M.op (σ (M.op (M.op x y) x)) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq186052
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq186052
    | exact resolve eq186052 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186052
  have eq186131 : x = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7371 eq186043
    | exact resolve eq186043 eq7371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7371 eq186043
  have eq186195 : (σ y) = (M.op (σ (k (M.op x y) (M.op x y))) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14381 eq186124
    | exact resolve eq186124 eq14381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14381 eq186124
  have eq186252 : (σ y) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq41 eq186195
    | exact resolve eq186195 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186195
  have eq186301 : (σ y) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq186252
    | exact resolve eq186252 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186252
  have eq191844 : (σ y) = (M.op (σ (M.op (k y y) (M.op x y))) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq186030 eq30347
    | exact resolve eq30347 eq186030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30347 eq186030
  have eq191913 : (σ y) = (M.op (σ (M.op (k y y) (M.op x y))) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq191844
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq191844
    | exact resolve eq191844 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191844
  have eq191966 : (σ y) = (M.op (σ (M.op (k x x) (M.op x y))) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq186131 eq191913
    | exact resolve eq191913 eq186131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186131 eq191913
  have eq191999 : (σ y) = (M.op (σ (M.op (M.op x y) y)) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7567 eq191966
    | exact resolve eq191966 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7567 eq191966
  have eq192024 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9488 eq191999
    | exact resolve eq191999 eq9488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191999
  have eq192042 : (σ y) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq192024
       have i₂ := eq10080 sF4 sF3
       grind)
    | exact superpose eq10080 eq192024
    | exact resolve eq192024 eq10080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10080 eq192024
  have eq192053 : (σ y) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14013 eq192042
    | exact resolve eq192042 eq14013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14013 eq192042
  have eq192477 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq186301 eq11915
    | exact resolve eq11915 eq186301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11915 eq186301
  have eq192650 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq192477
       have i₂ := eq183 sF3
       grind)
    | exact superpose eq183 eq192477
    | exact resolve eq192477 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192477
  have eq196843 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq192053 eq62852
    | exact resolve eq62852 eq192053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62852 eq192053
  have eq197025 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq196843
       have i₂ := eq183 sF3
       grind)
    | exact superpose eq183 eq196843
    | exact resolve eq196843 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196843
  have eq197134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq192650 eq197025
    | exact resolve eq197025 eq192650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192650 eq197025
  have eq197232 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq197134
       have r₂ := eq27
       grind)
    | exact resolve eq197134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197134
  have eq197316 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq197232
       grind)
    | exact superpose eq197232 eq36
    | exact resolve eq36 eq197232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197232
  have eq197324 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq197316
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq197316
    | exact resolve eq197316 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197316
  have eq197336 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq197324 eq813
    | exact resolve eq813 eq197324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197340 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq197324 eq809
    | (have j0 := eq809 (σ y) (σ x) x
       grind)
    | exact resolve eq809 eq197324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq197342 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq197324 eq831
    | (have j0 := eq831 (σ x) (σ y)
       grind)
    | exact resolve eq831 eq197324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq197324
  have eq197345 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq197342
    | exact resolve eq197342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197342
  have eq197346 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq26 eq197340
    | (have j0 := eq197340 X0
       grind)
    | exact resolve eq197340 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197340
  have eq197352 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq197345
    | exact resolve eq197345 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197345
  have eq197353 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq26 eq197346
    | (have j0 := eq197346 X0
       grind)
    | exact resolve eq197346 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197346
  have eq197355 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq26 eq197353
    | (have j0 := eq197353 X0
       grind)
    | exact resolve eq197353 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197353
  have eq197356 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq197336 eq197355
    | exact resolve eq197355 eq197336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197336 eq197355
  have eq197357 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1736 eq197356
    | (have j0 := eq197356 (σ y)
       grind)
    | exact resolve eq197356 eq1736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736 eq197356
  have eq197358 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7474 eq197357
    | exact resolve eq197357 eq7474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7474 eq197357
  have eq197359 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq197358
       have r₂ := eq197352
       grind)
    | exact resolve eq197358 eq197352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197352 eq197358
  have eq197431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq197359 eq185952
    | exact resolve eq185952 eq197359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq197431
  have eq197574 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq197511
       have r₂ := eq27
       grind)
    | exact resolve eq197511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197511
  have eq197682 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq197574 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq197574
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq197574
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq197574
       grind)
    | exact resolve eq13 eq197574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197724 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq197574 eq16539
    | exact resolve eq16539 eq197574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197574
  have eq197815 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7318 eq197724
    | exact resolve eq197724 eq7318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197724
  have eq197851 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq197682
       have r₂ := eq26
       grind)
    | exact resolve eq197682 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197682
  have eq197905 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq197815 eq197851
    | exact resolve eq197851 eq197815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197815 eq197851
  have eq197946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq185952 eq197905
    | exact resolve eq197905 eq185952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185952 eq197905
  have eq197983 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq197946
       have r₂ := eq27
       grind)
    | exact resolve eq197946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197946
  have eq198088 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq75770 y x x
       have i₂ := eq197983
       grind)
    | exact superpose eq197983 eq75770
    | exact resolve eq75770 eq197983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75770 eq197983
  have eq198109 : (M.op x y) = (M.op (M.op (k (M.op x y) (M.op x y)) (M.op x y)) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq198088 x
       have i₂ := eq53611 sF0 x y
       grind)
    | exact superpose eq53611 eq198088
    | exact resolve eq198088 eq53611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53611 eq198088
  have eq198185 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12304 eq198109
    | exact resolve eq198109 eq12304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12304 eq198109
  have eq198792 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq198185
       grind)
    | exact superpose eq198185 eq39
    | exact resolve eq39 eq198185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq198185
  have eq198926 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq198792
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq198792
    | exact resolve eq198792 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198792
  have eq198994 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq198926
    | exact resolve eq198926 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198926
  have eq199525 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq198994 eq197359
    | exact resolve eq197359 eq198994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197359
  have eq199603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq199525
  have eq199661 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq199603
       have r₂ := eq27
       grind)
    | exact resolve eq199603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199603
  have eq200521 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq199661 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq199661
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq199661
       grind)
    | exact resolve eq13 eq199661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200562 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq199661 eq16539
    | exact resolve eq16539 eq199661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199661
  have eq200653 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7318 eq200562
    | exact resolve eq200562 eq7318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7318 eq200562
  have eq200689 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq200521
       have r₂ := eq26
       grind)
    | exact resolve eq200521 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200521
  have eq200754 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq200689
    | exact resolve eq200689 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200689
  have eq200808 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq200653 eq200754
    | exact resolve eq200754 eq200653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200653 eq200754
  have eq200847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq198994 eq200808
    | exact resolve eq200808 eq198994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198994 eq200808
  have eq200880 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq200847
       have r₂ := eq27
       grind)
    | exact resolve eq200847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200847
  have eq200907 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq200880 eq28
    | exact resolve eq28 eq200880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq200961 : (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = (τ (M.op (k (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq200880 eq33255
    | exact resolve eq33255 eq200880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33255
  have eq200963 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq7220 eq200961
    | exact resolve eq200961 eq7220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7220 eq200961
  have eq201000 : (M.op (M.op x y) y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq9493 eq200963
    | exact resolve eq200963 eq9493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9493 eq200963
  have eq201054 : x = (M.op x y) := by
    first
    | exact superpose eq200907 eq29
    | exact resolve eq29 eq200907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq201055 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq200907 eq14
    | exact resolve eq14 eq200907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200907
  have eq201240 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq201054
       grind)
    | exact superpose eq201054 eq18
    | exact resolve eq18 eq201054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq201895 : (M.op x y) = (k y (M.op x y)) ∨ (M.op (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq201240
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq201240
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq201240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201916 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq201240 eq9488
    | exact resolve eq9488 eq201240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202028 : (σ (M.op (M.op x y) (M.op x y))) = (σ (M.op (k (M.op x y) (M.op x y)) y)) := by
    first
    | exact superpose eq201240 eq83958
    | exact resolve eq83958 eq201240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83958
  have eq202034 : (σ x) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq14323 eq202028
    | exact resolve eq202028 eq14323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14323 eq202028
  have eq202106 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq20 eq201916
    | exact resolve eq201916 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201916
  have eq202120 : (M.op x y) = (k y (M.op x y)) ∨ (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have j1 := eq12 (M.op x y) y
       grind)
    | (have r₁ := eq201895
       have r₂ := eq12 y (M.op x y)
       grind)
    | exact resolve eq201895 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201895
  have eq202122 : (σ x) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq202034
       have i₂ := eq183 sF0
       grind)
    | exact superpose eq183 eq202034
    | exact resolve eq202034 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202034
  have eq202166 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq200880 eq202106
    | exact resolve eq202106 eq200880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202106
  have eq202177 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq201240 eq202120
    | exact resolve eq202120 eq201240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201240 eq202120
  have eq202179 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq202122
    | exact resolve eq202122 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq202122
  have eq202213 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq200880 eq202179
    | exact resolve eq202179 eq200880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202179
  have eq202230 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq202213
    | exact resolve eq202213 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202213
  have eq202241 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq200880 eq202230
    | exact resolve eq202230 eq200880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202230
  have eq202245 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq202241
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq202241
    | exact resolve eq202241 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq202241
  have eq204989 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq202166 eq17669
    | exact resolve eq17669 eq202166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17669
  have eq205067 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq204989
    | exact resolve eq204989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq204989
  have eq222362 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq202177 eq36
    | exact resolve eq36 eq202177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq202177
  have eq222371 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq222362
    | exact resolve eq222362 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq222362
  have eq222377 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq200880 eq222371
    | exact resolve eq222371 eq200880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222371
  have eq222398 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq222377 eq813
    | exact resolve eq813 eq222377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq222377
  have eq222411 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq202245 eq222398
    | exact resolve eq222398 eq202245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222398
  have eq222412 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by grind
  clear eq222411
  have eq270432 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq222412 eq16963
    | exact resolve eq16963 eq222412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16963 eq222412
  have eq270514 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq205067 eq270432
    | exact resolve eq270432 eq205067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270432
  have eq270596 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq202166 eq270514
    | exact resolve eq270514 eq202166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202166 eq270514
  have eq270597 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq270596
  have eq270723 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq270597 eq16539
    | exact resolve eq16539 eq270597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16539 eq270597
  have eq270818 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq186 eq270723
    | exact resolve eq270723 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq270723
  have eq270903 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq270818
       have i₂ := eq201054
       grind)
    | exact superpose eq201054 eq270818
    | exact resolve eq270818 eq201054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201054 eq270818
  have eq271167 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq270903 eq27
    | exact resolve eq27 eq270903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270903
  have eq271445 : y = (M.op x y) := by
    first
    | (have r₁ := eq271167
       have r₂ := eq200880
       grind)
    | exact resolve eq271167 eq200880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271167
  have eq271520 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq271445
       grind)
    | exact superpose eq271445 eq24
    | exact resolve eq24 eq271445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq271592 : (M.op (k (σ y) (σ y)) (σ y)) = (σ (M.op (k (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq31735
       have i₂ := eq271445
       grind)
    | exact superpose eq271445 eq31735
    | exact resolve eq31735 eq271445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31735 eq271445
  have eq271689 : (σ (M.op (M.op x y) y)) = (M.op (k (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq201000 eq271592
    | exact resolve eq271592 eq201000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201000 eq271592
  have eq271760 : (σ x) = (σ y) := by
    first
    | exact superpose eq201055 eq271520
    | exact resolve eq271520 eq201055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201055 eq271520
  have eq271787 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq9488 eq271689
    | exact resolve eq271689 eq9488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9488 eq271689
  have eq271872 : (M.op (k (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq271760 eq271787
    | exact resolve eq271787 eq271760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271760 eq271787
  have eq271932 : (M.op (k (σ x) (σ x)) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13988 eq271872
    | exact resolve eq271872 eq13988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13988 eq271872
  have eq271967 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq205067 eq271932
    | exact resolve eq271932 eq205067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205067 eq271932
  have eq271987 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq202245 eq271967
    | exact resolve eq271967 eq202245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271967
  have eq271997 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq271987
       have i₂ := eq183 sF2
       grind)
    | exact superpose eq183 eq271987
    | exact resolve eq271987 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq271987
  have eq272001 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq202245 eq271997
    | exact resolve eq271997 eq202245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202245 eq271997
  have eq272558 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq272001 eq27
    | exact resolve eq27 eq272001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq272001
  have eq272840 : False := by grind
  exact eq272840

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxx_y_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (k y x) := by
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
  have eq78 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq120 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq146 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq147 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq146
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq146
    | exact resolve eq146 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq149 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq147
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq147
    | exact resolve eq147 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq147
  have eq188 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq149 eq16
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq428 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 X2) (M.op X3 X3)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X2 X0 X3
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq51 X0 X0 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq51
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq51 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq188
       have i₂ := eq439 X0 sF1
       grind)
    | (have i₁ := eq188
       have i₂ := eq439 sF1 x
       grind)
    | exact superpose eq439 eq188
    | exact resolve eq188 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq538 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq64
       have i₂ := eq439 X0 sF2
       grind)
    | (have i₁ := eq64
       have i₂ := eq439 sF2 x
       grind)
    | exact superpose eq439 eq64
    | exact resolve eq64 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq825 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k X2 X3) ∨ (M.op X3 X2) = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq104 X3 X2
       have i₂ := eq51 X0 X2 X1
       grind)
    | (have i₁ := eq104 X0 (M.op X2 X2)
       have i₂ := eq51 X2 X1 X2
       grind)
    | exact superpose eq51 eq104
    | (have j0 := eq104 X3 X2
       grind)
    | exact resolve eq104 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq104
  have eq9360 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) ≠ (M.op (M.op X2 X2) (M.op X3 X3)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq825 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq9369 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9360 X0 X1 x x
       have j1 := eq428 X1 X0 x x
       grind)
    | (have r₁ := eq9360 X1 X0 x x
       have r₂ := eq428 X0 X1 x x
       grind)
    | (have r₁ := eq9360 (M.op x x) (M.op x x) x x
       have r₂ := eq428 (M.op x x) (M.op x x) x x
       grind)
    | (have r₁ := eq9360 X1 (M.op (M.op x x) (M.op x x)) x x
       have r₂ := eq428 (M.op (M.op x x) (M.op x x)) X1 x x
       grind)
    | exact resolve eq9360 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq9360
  have eq10181 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq9369 y x
       grind)
    | exact superpose eq9369 eq120
    | (have j1 := eq9369 y x
       grind)
    | exact resolve eq120 eq9369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10289 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10181
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10181
    | exact resolve eq10181 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10181
  have eq10323 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq10289
    | exact resolve eq10289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10289
  have eq10336 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10323
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10323
    | exact resolve eq10323 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10323
  have eq10353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10336 eq9369
    | (have j0 := eq9369 (σ y) (σ x)
       grind)
    | exact resolve eq9369 eq10336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10354 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10353
    | exact resolve eq10353 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10353
  have eq10366 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10354
       have r₂ := eq27
       grind)
    | exact resolve eq10354 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10354
  have eq10373 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10366
    | exact resolve eq10366 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10366
  have eq10382 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10373 eq78
    | (have r₁ := eq78
       have r₂ := eq10373
       grind)
    | exact resolve eq78 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq10383 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10373 eq27
    | exact resolve eq27 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10384 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10382
  have eq10391 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10384 eq10336
    | exact resolve eq10336 eq10384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384
  have eq10409 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq10391
  have eq10423 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10409
       have r₂ := eq10383
       grind)
    | exact resolve eq10409 eq10383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10409
  have eq10429 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10423
       have i₂ := eq439 X0 sF2
       grind)
    | (have i₁ := eq10423
       have i₂ := eq439 sF2 x
       grind)
    | exact superpose eq439 eq10423
    | exact resolve eq10423 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10480 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10423 eq491
    | exact resolve eq491 eq10423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10488 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10423 eq538
    | exact resolve eq538 eq10423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq10423
  have eq10539 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10488
       have r₂ := eq10373
       grind)
    | exact resolve eq10488 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10373 eq10488
  have eq10544 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq10480
    | exact resolve eq10480 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10480
  have eq10857 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10544
       have i₂ := eq439 X0 sF0
       grind)
    | (have i₁ := eq10544
       have i₂ := eq439 sF0 x
       grind)
    | exact superpose eq439 eq10544
    | exact resolve eq10544 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10948 : x = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10544 eq10429
    | exact resolve eq10429 eq10544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10429 eq10544
  have eq10965 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq10948
  have eq11041 : x ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10965 eq10383
    | exact resolve eq10383 eq10965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10383 eq10965
  have eq11046 : x ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq11041
  have eq14663 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10539 eq10336
    | exact resolve eq10336 eq10539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10336 eq10539
  have eq14671 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14663
  have eq14793 : x = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14671 eq10857
    | exact resolve eq10857 eq14671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10857 eq14671
  have eq14808 : x = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq14793
  have eq14825 : x = (M.op x y) := by
    first
    | (have r₁ := eq14808
       have r₂ := eq11046
       grind)
    | exact resolve eq14808 eq11046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11046 eq14808
  have eq14997 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14825 eq20
    | exact resolve eq20 eq14825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq15000 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq14825 eq77
    | (have r₁ := eq77
       have r₂ := eq14825
       grind)
    | exact resolve eq77 eq14825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq15050 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq15000
  have eq15102 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14997
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14997
    | exact resolve eq14997 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14997
  have eq15142 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15102 eq26
    | exact resolve eq26 eq15102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq17014 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120
       have i₂ := eq15050
       grind)
    | exact superpose eq15050 eq120
    | exact resolve eq120 eq15050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15050
  have eq17052 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15102 eq17014
    | exact resolve eq17014 eq15102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17014
  have eq17061 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17052
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17052
    | exact resolve eq17052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17052
  have eq17068 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15102 eq17061
    | exact resolve eq17061 eq15102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17061
  have eq17103 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17068 eq9369
    | (have j0 := eq9369 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq9369 eq17068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17068
  have eq17104 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq17103
  have eq17113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15142 eq17104
    | exact resolve eq17104 eq15142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17104
  have eq17125 : x = (M.op x x) := by
    first
    | (have r₁ := eq17113
       have r₂ := eq27
       grind)
    | exact resolve eq17113 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17113
  have eq17142 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq17125
       have i₂ := eq439 X0 x
       grind)
    | (have i₁ := eq17125
       have i₂ := eq439 x X0
       grind)
    | exact superpose eq439 eq17125
    | exact resolve eq17125 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq17197 : (M.op (M.op x y) (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq491 x
       have i₂ := eq17125
       grind)
    | exact superpose eq17125 eq491
    | exact resolve eq491 eq17125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq17274 : (M.op x x) = (τ x) := by
    first
    | exact superpose eq14825 eq17197
    | exact resolve eq17197 eq14825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17197
  have eq17294 : x = (τ x) := by
    first
    | (have i₁ := eq17274
       have i₂ := eq17125
       grind)
    | exact superpose eq17125 eq17274
    | exact resolve eq17274 eq17125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17125 eq17274
  have eq17334 : x = (σ x) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq17294
       grind)
    | exact superpose eq17294 eq15
    | exact resolve eq15 eq17294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17294
  have eq17377 : x = (σ x) := by
    first
    | (have i₁ := eq17334
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17334
    | exact resolve eq17334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17334
  have eq17387 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq15102 eq17377
    | exact resolve eq17377 eq15102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17377
  have eq17423 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq17387 eq15142
    | exact resolve eq15142 eq17387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15142
  have eq17712 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq63
       have i₂ := eq17142 x
       grind)
    | exact superpose eq17142 eq63
    | exact resolve eq63 eq17142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq17818 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq17712
       have r₂ := eq14825
       grind)
    | exact resolve eq17712 eq14825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14825 eq17712
  have eq17971 : x = (k y x) := by
    first
    | (have i₁ := eq17818
       have i₂ := eq17142 y
       grind)
    | exact superpose eq17142 eq17818
    | exact resolve eq17818 eq17142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17142 eq17818
  have eq18247 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq17971
       grind)
    | exact superpose eq17971 eq120
    | exact resolve eq120 eq17971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq17971
  have eq18284 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq15102 eq18247
    | exact resolve eq18247 eq15102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18247
  have eq18295 : (σ x) = (k (σ y) x) := by
    first
    | exact superpose eq17387 eq18284
    | exact resolve eq18284 eq17387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18284
  have eq18302 : (σ x) = (k (σ y) x) := by
    first
    | (have i₁ := eq18295
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18295
    | exact resolve eq18295 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18295
  have eq18309 : (σ (M.op x y)) = (k (σ y) x) := by
    first
    | exact superpose eq15102 eq18302
    | exact resolve eq18302 eq15102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15102 eq18302
  have eq18316 : x = (k (σ y) x) := by
    first
    | exact superpose eq17387 eq18309
    | exact resolve eq18309 eq17387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18309
  have eq18359 : x = (M.op x (σ y)) ∨ x = (M.op x (σ y)) := by
    first
    | exact superpose eq18316 eq9369
    | (have j0 := eq9369 (σ y) x
       grind)
    | exact resolve eq9369 eq18316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9369 eq18316
  have eq18360 : x = (M.op x (σ y)) := by grind
  clear eq18359
  have eq18369 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17423 eq18360
    | exact resolve eq18360 eq17423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17423 eq18360
  have eq18388 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq18369 eq27
    | exact resolve eq27 eq18369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18369
  have eq18389 : False := by grind
  exact eq18389

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq92 sF2 sF3
       grind)
    | exact superpose eq92 eq56
    | (have j1 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq56 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq114 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq112
    | exact resolve eq112 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq116 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq114
    | exact resolve eq114 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37
  have eq155 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq407 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq44
    | exact resolve eq44 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq116
  have eq410 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq407
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq407
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq514 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq515 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq514
  have eq520 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq515 eq118
    | exact resolve eq118 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq524 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq520
  have eq531 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq524
       have r₂ := eq129
       grind)
    | exact resolve eq524 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq524
  have eq535 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq531 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq531
       grind)
    | exact resolve eq13 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq536 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq535
  have eq537 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq536
    | exact resolve eq536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq536
  have eq609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq537 eq118
    | exact resolve eq118 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq537
  have eq612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq609
  have eq616 : x = (M.op x y) := by
    first
    | (have r₁ := eq612
       have r₂ := eq27
       grind)
    | exact resolve eq612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq618 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq616 eq20
    | exact resolve eq20 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq622 : x ≠ x ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq616 eq74
    | (have r₁ := eq74
       have r₂ := eq616
       grind)
    | exact resolve eq74 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq628 : x = (M.op y x) ∨ x = (k x y) := by grind
  clear eq622
  have eq636 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq618
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq618
    | exact resolve eq618 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq648 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq636 eq410
    | exact resolve eq410 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq653 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq648
       have r₂ := eq27
       grind)
    | exact resolve eq648 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq665 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq653 eq155
    | exact resolve eq155 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq653
  have eq667 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq616 eq665
    | exact resolve eq665 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq943 : x = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq628
       have i₂ := eq667
       grind)
    | exact superpose eq667 eq628
    | exact resolve eq628 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq945 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq943
       grind)
    | exact superpose eq943 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq943
       grind)
    | exact resolve eq13 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq946 : (M.op x y) = (k x y) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq945
  have eq947 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq946
       have i₂ := eq667
       grind)
    | exact superpose eq667 eq946
    | exact resolve eq946 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq946
  have eq949 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq947
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq947
    | exact resolve eq947 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq947
  have eq951 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq616 eq949
    | exact resolve eq949 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq949
  have eq952 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq951
  have eq957 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq952 eq15
    | exact resolve eq15 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq974 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq957
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq957
    | exact resolve eq957 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq957
  have eq980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq636 eq974
    | exact resolve eq974 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq974
  have eq984 : False := by grind
  exact eq984

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq75 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq44
    | exact resolve eq44 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq81 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq78
    | exact resolve eq78 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq78
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X0) X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X1 X0)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq45
    | (have j1 := eq91 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq45 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq120
    | exact resolve eq120 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq121 eq91
    | (have j0 := eq91 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq91 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq121
  have eq185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq184
    | exact resolve eq184 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq188 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq185
       have r₂ := eq28
       grind)
    | exact resolve eq185 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq191 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq188 eq30
    | exact resolve eq30 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq188
  have eq204 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq191
    | exact resolve eq191 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq191
  have eq205 : x = y := by grind
  clear eq204
  have eq208 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq205
       grind)
    | exact superpose eq205 eq19
    | exact resolve eq19 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq209 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq205
       grind)
    | exact superpose eq205 eq25
    | exact resolve eq25 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq205
  have eq220 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq209
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq209
    | exact resolve eq209 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq209
  have eq224 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq220 eq27
    | exact resolve eq27 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq220
  have eq238 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq208
       grind)
    | exact superpose eq208 eq81
    | exact resolve eq81 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq208
  have eq243 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq238
    | exact resolve eq238 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq238
  have eq249 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq224 eq243
    | exact resolve eq243 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq243
  have eq250 : False := by grind
  exact eq250
