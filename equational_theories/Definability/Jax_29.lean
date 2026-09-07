import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation834`: `x = x ◇ ((y ◇ x) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_Equation834 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law834 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law834.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq57 (σ X0) (σ X1)
       grind)
    | exact superpose eq57 eq15
    | (have j1 := eq57 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq57 (τ X0) X1
       grind)
    | exact superpose eq57 eq18
    | (have j1 := eq57 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq57
  have eq488 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq76
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq488 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq488
    | (have j0 := eq488 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq488 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq914 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1016 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq914
       have i₂ := eq519 x y
       grind)
    | exact superpose eq519 eq914
    | (have j1 := eq519 (σ x) (σ y)
       grind)
    | (have r₁ := eq914
       have r₂ := eq519 x y
       grind)
    | (have r₁ := eq914
       have r₂ := eq519 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq914
       have r₂ := eq519 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq914 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq914
  have eq1017 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1016
  have eq1087 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1017
       grind)
    | exact superpose eq1017 eq10
    | exact resolve eq10 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1123 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1087
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1087
    | exact resolve eq1087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1124 : x = y := by grind
  clear eq1123
  have eq1248 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1124
       grind)
    | exact superpose eq1124 eq16
    | exact resolve eq16 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1249 : False := by grind
  exact eq1249

/-- `Equation834`: `x = x ◇ ((y ◇ x) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation834 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law834 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law834.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ X1 = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X2
       have i₂ := eq14 X1 X2
       grind)
    | (have i₁ := eq14 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | (have j0 := eq14 X1 X2
       have j1 := eq14 X1 X2
       grind)
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X0 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X1 X1 X2
       have j1 := eq56 X1 X1 X2
       grind)
    | (have r₁ := eq43 X0 X1 X2
       have r₂ := eq56 X0 X1 X2
       grind)
    | (have r₁ := eq43 X1 X0 X2
       have r₂ := eq56 X0 X1 X2
       grind)
    | (have r₁ := eq43 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq56 X0 X1 X2
       grind)
    | exact resolve eq43 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq56
  have eq118 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq119 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq225 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq120 (σ X0) (σ X1)
       grind)
    | exact superpose eq120 eq15
    | (have j1 := eq120 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq120 (τ X0) X1
       grind)
    | exact superpose eq120 eq18
    | (have j1 := eq120 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq120
  have eq537 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq227 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq227
    | exact resolve eq227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq569 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq537
    | (have j0 := eq537 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq537 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq2142 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq225 x y
       grind)
    | exact superpose eq225 eq16
    | (have j1 := eq225 x y
       grind)
    | exact resolve eq16 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq2255 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2142
       have i₂ := eq569 x y
       grind)
    | exact superpose eq569 eq2142
    | (have j1 := eq569 (σ x) (σ y)
       grind)
    | (have r₁ := eq2142
       have r₂ := eq569 x y
       grind)
    | (have r₁ := eq2142
       have r₂ := eq569 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2142
       have r₂ := eq569 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2142 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq2142
  have eq2256 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2255
  have eq2354 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2256
       grind)
    | exact superpose eq2256 eq10
    | exact resolve eq10 eq2256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq2399 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2354
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2354
    | exact resolve eq2354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq2400 : x = y := by grind
  clear eq2399
  have eq2484 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2400
       grind)
    | exact superpose eq2400 eq16
    | exact resolve eq16 eq2400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400
  have eq2485 : False := by grind
  exact eq2485

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_x_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq39 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X1 ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq44 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 X2) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq54 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 X2) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq44 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq44 (k X0 X1) X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 (k X0 X1) X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43 (M.op X0 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq58 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq54 X0 X1 X0
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq54 (k X1 X0) X1 x
       grind)
    | (have r₁ := eq55 X0 X0
       have r₂ := eq54 X0 (k X0 X0) x
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq54 X0 X1 x
       grind)
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq59 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq58 (τ X1) X0
       grind)
    | exact superpose eq58 eq19
    | (have j1 := eq58 (τ X1) X0
       grind)
    | exact resolve eq19 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq86 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 (M.op X1 (M.op X0 (M.op X2 (M.op X3 (M.op X0 (M.op (M.op X4 X5) (M.op X3 X5))))))))) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20 X2 X1 X0 (M.op X3 (M.op X0 (M.op (M.op X4 X5) (M.op X3 X5))))
       have i₂ := eq20 X3 X0 X4 X5
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq107 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 (M.op X0 X1) X0 X1
       have i₂ := eq95 (M.op X0 X1)
       grind)
    | exact superpose eq95 eq21
    | exact resolve eq21 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq180 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq217 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X2) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X1
       have i₂ := eq53 X1 X2 X0
       grind)
    | (have i₁ := eq95 X0
       have i₂ := eq53 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq95
    | (have j1 := eq53 X1 X2 X0
       grind)
    | exact resolve eq95 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq299 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X3 X1) X1)) = X1 ∨ (M.op X1 (M.op (M.op X2 X1) X0)) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X1
       have i₂ := eq40 X1 X3 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq40 X0 X1 (M.op X0 X2)
       grind)
    | exact superpose eq40 eq9
    | (have j1 := eq40 X1 X3 X0
       grind)
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq401 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op X3 X2))) = X3 ∨ (M.op X1 (M.op X0 (M.op X1 X2))) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq41 X2 X3 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq41 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq41 eq9
    | (have j1 := eq41 X2 X3 X0
       grind)
    | exact resolve eq9 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq529 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X0 X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (M.op (M.op X1 (M.op X0 X0)) X0)
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq74
    | (have j0 := eq74 X0 (M.op (M.op X1 (M.op X0 X0)) X0)
       grind)
    | (have r₁ := eq74 X0 (M.op (M.op X1 (M.op X0 X0)) X0)
       have r₂ := eq107 X0 X1
       grind)
    | exact resolve eq74 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq533 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 (M.op X0 X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq529 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq636 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq780 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X2 X1
       have i₂ := eq636 X1 X0
       grind)
    | exact superpose eq636 eq9
    | exact resolve eq9 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq48 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq48 X1 X1
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq48 X0 X1
       grind)
    | exact superpose eq48 eq10
    | (have j1 := eq48 X0 X1
       grind)
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq48 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq925 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq944 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq838 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq977 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq944 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq944 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq944 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1465 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq180 X0 (σ X1)
       grind)
    | exact superpose eq180 eq25
    | (have j1 := eq180 (τ X0) X1
       grind)
    | exact resolve eq25 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq180
  have eq1506 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (M.op (M.op X1 (σ (k X0 X0))) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 (σ X0) X1
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq533
    | (have j1 := eq48 X0 X0
       grind)
    | exact resolve eq533 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq533
  have eq1542 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (M.op (M.op X1 (σ (k X0 X0))) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1506 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq1547 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (M.op (M.op X1 (σ (k X0 X0))) (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1542 X0 X1
       have j1 := eq12 (σ X0) (M.op (M.op X1 (σ (k X0 X0))) (σ X0))
       grind)
    | (have r₁ := eq1542 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq1542 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1560 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (k (σ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq977 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq977
    | (have j0 := eq977 (σ X0) X1
       grind)
    | exact resolve eq977 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq2198 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq928 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq928
    | (have j0 := eq928 (τ X0)
       grind)
    | exact resolve eq928 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq2202 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2198 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2198
    | (have j0 := eq2198 X0
       grind)
    | exact resolve eq2198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2208 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2202 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2202
    | (have j0 := eq2202 X0
       grind)
    | exact resolve eq2202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2232 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2278 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2232 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2232
    | (have j0 := eq2232 X0 X1
       grind)
    | exact resolve eq2232 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq2385 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7636 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2208 (τ X0)
       have i₂ := eq1465 X0 (τ X0)
       grind)
    | exact superpose eq1465 eq2208
    | (have j0 := eq2208 (τ X0)
       have j1 := eq1465 X0 x
       grind)
    | (have r₁ := eq2208 (τ X0)
       have r₂ := eq1465 X0 (τ X0)
       grind)
    | exact resolve eq2208 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq7680 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7636
  have eq24094 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7680 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7680
    | (have j0 := eq7680 (σ X0)
       grind)
    | exact resolve eq7680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7680
  have eq24268 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24094 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq24094
    | (have j0 := eq24094 X0
       grind)
    | exact resolve eq24094 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24094
  have eq27576 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op X1 X0) X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq299 X0 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq27577 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27576 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27576
  have eq27585 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27577 X0 X1
       have i₂ := eq636 X0 X1
       grind)
    | exact superpose eq636 eq27577
    | (have j0 := eq27577 X0 X1
       grind)
    | exact resolve eq27577 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27577
  have eq30128 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X1 (M.op X0 X1))) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq401 X1 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq30129 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30128 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30128
  have eq36300 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) (M.op (M.op X1 (k (σ (τ X0)) X0)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1547 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1547
    | exact resolve eq1547 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq36433 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 (k X0 X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36300 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36300
    | exact resolve eq36300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36300
  have eq38586 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq886 X1 X1
       have i₂ := eq68 X1 X1
       grind)
    | exact superpose eq68 eq886
    | (have j0 := eq886 X0 X1
       have j1 := eq68 X0 X1
       grind)
    | exact resolve eq886 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq886
  have eq38764 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq38586 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38586
  have eq38794 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38764 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq38764
    | (have j0 := eq38764 X0 X1
       grind)
    | exact resolve eq38764 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38764
  have eq49754 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq24268 X0
       grind)
    | exact superpose eq24268 eq95
    | (have j1 := eq24268 X0
       grind)
    | exact resolve eq95 eq24268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24268
  have eq190651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2385
       have i₂ := eq2278 y x
       grind)
    | exact superpose eq2278 eq2385
    | (have j1 := eq2278 y x
       grind)
    | (have r₁ := eq2385
       have r₂ := eq2278 y x
       grind)
    | exact resolve eq2385 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278 eq2385
  have eq190652 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by grind
  clear eq190651
  have eq192737 : (M.op x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq190652
       grind)
    | exact superpose eq190652 eq10
    | exact resolve eq10 eq190652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190652
  have eq192812 : x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq192737
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq192737
    | exact resolve eq192737 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192737
  have eq192813 : x = (k x y) := by
    first
    | (have j1 := eq74 x y
       grind)
    | (have r₁ := eq192812
       have r₂ := eq74 x y
       grind)
    | exact resolve eq192812 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq192812
  have eq200580 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30129 X1 X0
       have i₂ := eq27585 X0 X1
       grind)
    | exact superpose eq27585 eq30129
    | (have j0 := eq30129 X0 X0
       have j1 := eq27585 X0 X1
       grind)
    | exact resolve eq30129 eq27585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30129
  have eq200652 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq200580 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200580
  have eq201354 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27585 X1 X0
       have i₂ := eq200652 X1 X0
       grind)
    | exact superpose eq200652 eq27585
    | (have j0 := eq27585 X1 X1
       have j1 := eq200652 X0 X1
       grind)
    | exact resolve eq27585 eq200652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27585
  have eq201561 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq200652 (σ X0) X1
       grind)
    | exact superpose eq200652 eq15
    | (have j1 := eq200652 (σ X0) X1
       grind)
    | exact resolve eq15 eq200652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200652
  have eq201578 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq201354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201354
  have eq202797 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq36433 X1 X0
       have i₂ := eq201578 (k X1 X1) X0
       grind)
    | exact superpose eq201578 eq36433
    | (have j1 := eq201578 X0 X0
       grind)
    | exact resolve eq36433 eq201578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36433 eq201578
  have eq334245 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq201561 X0 X1
       grind)
    | exact superpose eq201561 eq95
    | (have j1 := eq201561 (k X0 X0) (σ X0)
       grind)
    | exact resolve eq95 eq201561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq201561
  have eq407651 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq334245 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq334245
    | (have j0 := eq334245 (k (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq334245 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334245
  have eq407752 : ∀ X0 X1 : G, (M.op X0 (k (σ (τ X0)) X0)) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq407651 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq407651
    | (have j0 := eq407651 (k (σ (τ X0)) X0) X0
       grind)
    | exact resolve eq407651 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq407651
  have eq407758 : ∀ X0 X1 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq407752 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq407752
    | (have j0 := eq407752 (k X0 X0) X0
       grind)
    | exact resolve eq407752 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407752
  have eq412324 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq407758 X0 (M.op X0 X1)
       grind)
    | exact superpose eq407758 eq124
    | (have j1 := eq407758 X0 X1
       grind)
    | exact resolve eq124 eq407758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq415601 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X0 X1 x x x
       have i₂ := eq412324 X0 (M.op X1 (M.op x (M.op X0 (M.op (M.op x x) (M.op x x)))))
       grind)
    | exact superpose eq412324 eq86
    | (have j1 := eq412324 X0 X1
       grind)
    | exact resolve eq86 eq412324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq412324
  have eq426450 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (k X1 X1)) = X1 ∨ (M.op X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq415601 X1 X0
       have i₂ := eq407758 X1 X0
       grind)
    | exact superpose eq407758 eq415601
    | (have j0 := eq415601 X1 X1
       have j1 := eq407758 X1 X1
       grind)
    | exact resolve eq415601 eq407758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407758 eq415601
  have eq426612 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq426450 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426450
  have eq431636 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq426612 (k X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426612
  have eq431637 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq431636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431636
  have eq435898 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq431637 (τ X0)
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq431637
    | exact resolve eq431637 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq435907 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (k X0 X0)
       have i₂ := eq431637 X0
       grind)
    | exact superpose eq431637 eq9
    | exact resolve eq9 eq431637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435959 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (k X0 X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0 (k X0 X0) x
       have i₂ := eq431637 X0
       grind)
    | exact superpose eq431637 eq780
    | exact resolve eq780 eq431637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431637
  have eq436377 : ∀ X0 : G, x = (M.op x y) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq192813
       have i₂ := eq217 y x X0
       grind)
    | exact superpose eq217 eq192813
    | (have j1 := eq217 y x X0
       grind)
    | exact resolve eq192813 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq436436 : ∀ X0 : G, x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq436377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436377
  have eq437144 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op X1 (τ (k X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ (k X0 X0))
       have i₂ := eq435898 X0
       grind)
    | exact superpose eq435898 eq9
    | exact resolve eq9 eq435898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435898
  have eq437360 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq435907 x X0
       have i₂ := eq436436 x
       grind)
    | exact superpose eq436436 eq435907
    | exact resolve eq435907 eq436436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435907
  have eq437820 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq435959 x X0
       have i₂ := eq436436 x
       grind)
    | exact superpose eq436436 eq435959
    | exact resolve eq435959 eq436436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435959 eq436436
  have eq437921 : ∀ X0 : G, x = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq437820 X0
       have i₂ := eq636 x X0
       grind)
    | exact superpose eq636 eq437820
    | exact resolve eq437820 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437820
  have eq442653 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq437360 X0
       have i₂ := eq437921 X0
       grind)
    | exact superpose eq437921 eq437360
    | exact resolve eq437360 eq437921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437360
  have eq442731 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq442653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442653
  have eq442738 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq437921 X0
       have i₂ := eq442731 X0
       grind)
    | exact superpose eq442731 eq437921
    | exact resolve eq437921 eq442731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437921 eq442731
  have eq442952 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq442738 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442738
  have eq443477 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq442952 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442952
  have eq443478 : x = (M.op x y) := by grind
  clear eq443477
  have eq449955 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38794 x y
       grind)
    | exact superpose eq38794 eq16
    | (have j1 := eq38794 x y
       grind)
    | exact resolve eq16 eq38794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38794
  have eq449961 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq449955
       have i₂ := eq192813
       grind)
    | exact superpose eq192813 eq449955
    | exact resolve eq449955 eq192813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192813 eq449955
  have eq449964 : (σ x) ≠ (σ x) ∨ y = (k x x) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq449961
       have i₂ := eq443478
       grind)
    | exact superpose eq443478 eq449961
    | exact resolve eq449961 eq443478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449961
  have eq449965 : (σ x) = (σ (k x x)) ∨ y = (k x x) := by grind
  clear eq449964
  have eq450018 : (k x x) = (τ (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq449965
       grind)
    | exact superpose eq449965 eq10
    | exact resolve eq10 eq449965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449965
  have eq450079 : y = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq450018
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq450018
    | exact resolve eq450018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450018
  have eq450168 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq49754 x
       have i₂ := eq450079
       grind)
    | exact superpose eq450079 eq49754
    | (have j0 := eq49754 x
       grind)
    | exact resolve eq49754 eq450079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49754 eq450079
  have eq450326 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq2208 x
       grind)
    | (have r₁ := eq450168
       have r₂ := eq2208 x
       grind)
    | exact resolve eq450168 eq2208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208 eq450168
  have eq458508 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq450326
       grind)
    | exact superpose eq450326 eq16
    | exact resolve eq16 eq450326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450326
  have eq458574 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq458508
       have i₂ := eq443478
       grind)
    | exact superpose eq443478 eq458508
    | exact resolve eq458508 eq443478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458508
  have eq458575 : x = (M.op x x) := by grind
  clear eq458574
  have eq458657 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq458575
       grind)
    | exact superpose eq458575 eq9
    | exact resolve eq9 eq458575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458713 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq780 x x x
       have i₂ := eq458575
       grind)
    | exact superpose eq458575 eq780
    | exact resolve eq780 eq458575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458765 : x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq202797 x x
       have i₂ := eq458575
       grind)
    | exact superpose eq458575 eq202797
    | exact resolve eq202797 eq458575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202797 eq458575
  have eq458769 : x = (k x x) := by grind
  clear eq458765
  have eq458785 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq458713 X0
       have i₂ := eq636 x X0
       grind)
    | exact superpose eq636 eq458713
    | exact resolve eq458713 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq458713
  have eq458862 : ∀ X0 : G, (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (k (σ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq1560 x X0
       have i₂ := eq458769
       grind)
    | exact superpose eq458769 eq1560
    | (have j0 := eq1560 x X0
       grind)
    | exact resolve eq1560 eq458769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560 eq458769
  have eq458992 : ∀ X0 : G, (σ (σ x)) = (k (σ (σ x)) X0) := by
    intro X0
    first
    | (have j0 := eq458862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458862
  have eq463003 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq458657 X0
       have i₂ := eq458785 X0
       grind)
    | exact superpose eq458785 eq458657
    | exact resolve eq458657 eq458785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458657 eq458785
  have eq463339 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X1 x) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq780 X1 x X0
       have i₂ := eq463003 X0
       grind)
    | exact superpose eq463003 eq780
    | exact resolve eq780 eq463003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq463588 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq463339 X0 X0
       have i₂ := eq463003 X0
       grind)
    | exact superpose eq463003 eq463339
    | exact resolve eq463339 eq463003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463003 eq463339
  have eq466008 : ∀ X0 : G, (M.op X0 (M.op (τ (σ (σ x))) (M.op X0 (τ (σ (σ x)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq437144 (σ (σ x)) X0
       have i₂ := eq458992 (σ (σ x))
       grind)
    | exact superpose eq458992 eq437144
    | exact resolve eq437144 eq458992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437144 eq458992
  have eq466063 : ∀ X0 : G, (M.op X0 (τ (σ (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq466008 X0
       have i₂ := eq463588 X0 (τ (σ (σ x)))
       grind)
    | exact superpose eq463588 eq466008
    | exact resolve eq466008 eq463588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466008
  have eq466093 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq466063 X0
       have i₂ := eq10 (σ x)
       grind)
    | exact superpose eq10 eq466063
    | exact resolve eq466063 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466063
  have eq466284 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq463588 X0 (σ x)
       have i₂ := eq466093 X0
       grind)
    | exact superpose eq466093 eq463588
    | exact resolve eq463588 eq466093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463588 eq466093
  have eq466474 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq466284 (σ y)
       grind)
    | exact superpose eq466284 eq16
    | exact resolve eq16 eq466284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466284
  have eq466945 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq466474
       have i₂ := eq443478
       grind)
    | exact superpose eq443478 eq466474
    | exact resolve eq466474 eq443478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443478 eq466474
  have eq466946 : False := by grind
  exact eq466946

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_x_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq25 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq25 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq27 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq26 X0 X1 X2
       have j1 := eq12 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       grind)
    | (have r₁ := eq26 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X1 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq60 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X2) (M.op (τ X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 X2) (M.op (τ X0) X2))
       have i₂ := eq27 (τ X0) X1 X2
       grind)
    | exact superpose eq27 eq17
    | exact resolve eq17 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq64 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 X2) (M.op (τ X0) X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq87 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq9
    | exact resolve eq9 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq87 X0
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq107 X0
       have j1 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq107 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq107 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq111 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X0 X0)))) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X1 X2 X0 (M.op X0 X0)
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq20
    | exact resolve eq20 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq134 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq33 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq108 (σ X0)
       grind)
    | exact superpose eq108 eq33
    | exact resolve eq33 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq140 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq134 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq134
    | exact resolve eq134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq148 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq44 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq44 eq15
    | (have j1 := eq44 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X2 (σ X0)) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq41 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq41 eq15
    | (have j1 := eq41 (σ X0) X2 (M.op (M.op X2 (σ X0)) (σ X0))
       grind)
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq259 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0) ∨ (M.op X0 X4) = (k X0 X4) ∨ (M.op X0 X4) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X4
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq42
    | (have j0 := eq42 X0 X1 X4
       grind)
    | exact resolve eq42 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37 x y
       grind)
    | exact superpose eq37 eq16
    | (have j1 := eq37 x x
       grind)
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 (σ X0)
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq108
    | (have j1 := eq37 X0 X0
       grind)
    | exact resolve eq108 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq108
  have eq370 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq330 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq375 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq370 X0
       have j1 := eq12 (σ X0) (σ (k X0 X0))
       grind)
    | (have r₁ := eq370 X0
       have r₂ := eq12 (σ X0) x
       grind)
    | exact resolve eq370 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq379 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq375
    | exact resolve eq375 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq390 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq10
    | exact resolve eq10 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq403 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq390 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq390
    | exact resolve eq390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq489 : ∀ X0 X1 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X1 (M.op X0 (M.op X1 X0))) = X1 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1 (k X0 X0)
       have i₂ := eq403 X0
       grind)
    | exact superpose eq403 eq42
    | (have j0 := eq42 X0 X1 (k X0 X0)
       grind)
    | exact resolve eq42 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq403
  have eq498 : ∀ X0 X1 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X1 (M.op X0 (M.op X1 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq489 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq551 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 X2) (M.op (τ (τ X0)) X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op X1 X2) (M.op (τ (τ X0)) X2)))
       have i₂ := eq64 (τ X0) X1 X2
       grind)
    | exact superpose eq64 eq17
    | exact resolve eq17 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq64
  have eq562 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op (M.op X1 X2) (M.op (τ (τ X0)) X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq551 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq551
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq780 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq100
    | exact resolve eq100 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq894 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X2 X1
       have i₂ := eq780 X1 X0
       grind)
    | exact superpose eq780 eq9
    | exact resolve eq9 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X1
       have i₂ := eq780 X1 X0
       grind)
    | exact superpose eq780 eq13
    | (have j0 := eq13 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X1 X0) X0
       have r₂ := eq780 X0 X1
       grind)
    | exact resolve eq13 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq912 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq895 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq913 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq912 X0 X1
       have j1 := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq912 X0 X1
       have r₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact resolve eq912 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq10185 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (k (σ X0) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq148 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq12984 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq329
       have i₂ := eq44 x X0 y
       grind)
    | exact superpose eq44 eq329
    | (have j1 := eq44 x X0 y
       grind)
    | exact resolve eq329 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq329
  have eq12985 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12984 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12984
  have eq24215 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (M.op (M.op X2 (σ X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq211 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq24217 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (M.op X2 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24215 X0 X1 X2
       have i₂ := eq780 (σ X0) X2
       grind)
    | exact superpose eq780 eq24215
    | (have j0 := eq24215 X0 X1 X2
       grind)
    | exact resolve eq24215 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24215
  have eq28285 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X1 X2) (M.op X3 X2)))) = X3 ∨ (M.op X3 X4) = (k X3 X4) ∨ (M.op X3 X4) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X3 X0 X1 X2
       have i₂ := eq259 X3 X0 X1 X2 X4
       grind)
    | exact superpose eq259 eq20
    | (have j1 := eq259 X3 X1 X2 X3 X4
       grind)
    | exact resolve eq20 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq259
  have eq55334 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X0 X1
       have i₂ := eq498 X0 X0
       grind)
    | exact superpose eq498 eq111
    | (have j1 := eq498 X0 X1
       grind)
    | exact resolve eq111 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq55533 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55334 X0 X1
       have i₂ := eq780 X0 X1
       grind)
    | exact superpose eq780 eq55334
    | (have j0 := eq55334 X0 X1
       grind)
    | exact resolve eq55334 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55334
  have eq56801 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 X1
       have i₂ := eq55533 X0 X1
       grind)
    | exact superpose eq55533 eq498
    | (have j0 := eq498 X0 X1
       have j1 := eq55533 X0 X1
       grind)
    | exact resolve eq498 eq55533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq57154 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq56801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56801
  have eq59080 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (k X1 X1)) = X1 ∨ (M.op X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55533 X1 X0
       have i₂ := eq57154 X1 X0
       grind)
    | exact superpose eq57154 eq55533
    | (have j0 := eq55533 X1 X1
       have j1 := eq57154 X0 X1
       grind)
    | exact resolve eq55533 eq57154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55533 eq57154
  have eq59529 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq59080 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59080
  have eq63279 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq59529 (k X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59529
  have eq63280 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq63279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63279
  have eq64657 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63280 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq63280
    | exact resolve eq63280 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64663 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63280 (τ X0)
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq63280
    | exact resolve eq63280 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64790 : ∀ X0 X1 : G, (k X1 (σ (σ (M.op X0 (M.op (τ (τ X1)) (k X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq562 X1 X0 (k X0 X0)
       have i₂ := eq63280 X0
       grind)
    | exact superpose eq63280 eq562
    | exact resolve eq562 eq63280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq64792 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (k X0 X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq894 X0 (k X0 X0) x
       have i₂ := eq63280 X0
       grind)
    | exact superpose eq63280 eq894
    | exact resolve eq894 eq63280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66707 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 (σ (k X0 X0))) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq894 (σ X0) (σ (k X0 X0)) x
       have i₂ := eq64657 X0
       grind)
    | exact superpose eq64657 eq894
    | exact resolve eq894 eq64657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64657
  have eq68230 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq64663 (τ X0)
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq64663
    | exact resolve eq64663 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68249 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op X1 (τ (k X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ (k X0 X0))
       have i₂ := eq64663 X0
       grind)
    | exact superpose eq64663 eq9
    | exact resolve eq9 eq64663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68379 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (M.op X1 (τ (k X0 X0))) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq894 (τ X0) (τ (k X0 X0)) x
       have i₂ := eq64663 X0
       grind)
    | exact superpose eq64663 eq894
    | exact resolve eq894 eq64663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64663
  have eq84534 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (τ X0)) (M.op X1 (τ (τ (k X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (τ X0)) (τ (τ (k X0 X0)))
       have i₂ := eq68230 X0
       grind)
    | exact superpose eq68230 eq9
    | exact resolve eq9 eq68230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68230
  have eq163336 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (k (σ (τ X0)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10185 (τ X0) (τ X1) X2
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq10185
    | (have j0 := eq10185 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq10185 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163550 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (k (σ (τ X0)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163336 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq163336
    | (have j0 := eq163336 X0 X1 X2
       grind)
    | exact resolve eq163336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163336
  have eq163597 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (k (σ (τ X0)) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163550 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq163550
    | (have j0 := eq163550 X0 X1 X2
       grind)
    | exact resolve eq163550 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163550
  have eq163613 : ∀ X0 X1 X2 : G, (k X0 X2) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163597 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq163597
    | (have j0 := eq163597 X0 X1 X2
       grind)
    | exact resolve eq163597 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163597
  have eq163625 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X2) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163613 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq163613
    | (have j0 := eq163613 X0 X1 X2
       grind)
    | exact resolve eq163613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163613
  have eq163632 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (k X0 X2) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163625 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq163625
    | (have j0 := eq163625 X0 X1 X2
       grind)
    | exact resolve eq163625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163625
  have eq262261 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X2 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24217 (τ X0) (τ X1) X2
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq24217
    | (have j0 := eq24217 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq24217 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq24217
  have eq262554 : ∀ X0 X1 X2 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X2 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262261 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq262261
    | (have j0 := eq262261 X0 X1 X2
       grind)
    | exact resolve eq262261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262261
  have eq262621 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (M.op X2 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262554 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq262554
    | (have j0 := eq262554 X0 X1 X2
       grind)
    | exact resolve eq262554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262554
  have eq262645 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262621 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq262621
    | (have j0 := eq262621 X0 X1 X2
       grind)
    | exact resolve eq262621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262621
  have eq262663 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 (M.op X2 X0)) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262645 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq262645
    | (have j0 := eq262645 X0 X1 X2
       grind)
    | exact resolve eq262645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262645
  have eq262675 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 (M.op X2 X0)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262663 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq262663
    | (have j0 := eq262663 X0 X1 X2
       grind)
    | exact resolve eq262663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262663
  have eq262867 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq262675 X0 (τ (M.op (σ X0) (σ X0))) X1
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq262675
    | (have j0 := eq262675 X0 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq262675 X0 (τ (M.op (σ X0) (σ X0))) x
       have r₂ := eq140 X0
       grind)
    | exact resolve eq262675 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262675
  have eq263070 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq262867 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262867
  have eq264040 : ∀ X0 X1 X4 : G, (M.op X0 X4) = (k X0 X4) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X4) = X0 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq19 X0 X1 x x
       have i₂ := eq28285 X1 x x X0 X4
       grind)
    | exact superpose eq28285 eq19
    | (have j1 := eq28285 X0 X1 x X0 X4
       grind)
    | exact resolve eq19 eq28285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28285
  have eq266028 : ∀ X0 X1 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0
       have i₂ := eq264040 X0 X1 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq264040 eq140
    | (have j1 := eq264040 X0 X1 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq140 eq264040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq267400 : ∀ X0 X1 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq266028 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266028
  have eq279307 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (τ (M.op (σ X1) (σ X1)))) = X1 ∨ (M.op X1 (τ (M.op (σ X1) (σ X1)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq263070 X1 X0
       have i₂ := eq267400 X1 X0
       grind)
    | exact superpose eq267400 eq263070
    | (have j0 := eq263070 X1 X1
       have j1 := eq267400 X1 X1
       grind)
    | exact resolve eq263070 eq267400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263070 eq267400
  have eq279499 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 (τ (M.op (σ X1) (σ X1)))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq279307 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279307
  have eq280080 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq279499 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279499
  have eq280081 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq280080 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280080
  have eq280131 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq280081 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq280081
    | exact resolve eq280081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280081
  have eq280406 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op X1 (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq280131 X0
       grind)
    | exact superpose eq280131 eq9
    | exact resolve eq9 eq280131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280131
  have eq281452 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq913 (σ x) (σ y)
       have i₂ := eq12985 X0
       grind)
    | exact superpose eq12985 eq913
    | (have j1 := eq12985 X0
       grind)
    | exact resolve eq913 eq12985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12985
  have eq281453 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq281452 X0
       have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq281452 X0
       have r₂ := eq12 (σ x) x
       grind)
    | exact resolve eq281452 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281452
  have eq281454 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq281453 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq281453
    | (have j0 := eq281453 X0
       grind)
    | exact resolve eq281453 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281453
  have eq295067 : ∀ X0 : G, (k x y) = (τ (σ x)) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq281454 X0
       grind)
    | exact superpose eq281454 eq10
    | (have j1 := eq281454 X0
       grind)
    | exact resolve eq10 eq281454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281454
  have eq295101 : ∀ X0 : G, x = (k x y) ∨ x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq295067 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq295067
    | (have j0 := eq295067 y
       grind)
    | exact resolve eq295067 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295067
  have eq295102 : ∀ X0 : G, x = (k x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq295101 X0
       have j1 := eq163632 x y X0
       grind)
    | (have r₁ := eq295101 X0
       have r₂ := eq163632 x y x
       grind)
    | (have r₁ := eq295101 x
       have r₂ := eq163632 x x x
       grind)
    | exact resolve eq295101 eq163632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163632 eq295101
  have eq295178 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63280 x
       have i₂ := eq295102 x
       grind)
    | exact superpose eq295102 eq63280
    | exact resolve eq63280 eq295102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63280
  have eq295193 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq64792 x X0
       have i₂ := eq295102 x
       grind)
    | exact superpose eq295102 eq64792
    | exact resolve eq64792 eq295102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64792 eq295102
  have eq295312 : ∀ X0 : G, x = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq295193 X0
       have i₂ := eq780 x X0
       grind)
    | exact superpose eq780 eq295193
    | exact resolve eq295193 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295193
  have eq295415 : x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq913 x y
       have i₂ := eq295178
       grind)
    | exact superpose eq295178 eq913
    | exact resolve eq913 eq295178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq295178
  have eq295478 : x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq295415
       have r₂ := eq12 x x
       grind)
    | exact resolve eq295415 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295415
  have eq295559 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10185 x y X0
       have i₂ := eq295478
       grind)
    | exact superpose eq295478 eq10185
    | (have j0 := eq10185 x y X0
       grind)
    | exact resolve eq10185 eq295478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10185
  have eq295567 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq264040 x X0 y
       have i₂ := eq295478
       grind)
    | exact superpose eq295478 eq264040
    | (have j0 := eq264040 x X0 y
       grind)
    | exact resolve eq264040 eq295478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264040 eq295478
  have eq295570 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq295567 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295567
  have eq295576 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq295559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295559
  have eq297551 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq295312 X0
       have i₂ := eq295570 X0
       grind)
    | exact superpose eq295570 eq295312
    | exact resolve eq295312 eq295570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295312 eq295570
  have eq297803 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq297551 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297551
  have eq298750 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq297803 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297803
  have eq298751 : x = (M.op x y) := by grind
  clear eq298750
  have eq312413 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq295576 X0
       grind)
    | exact superpose eq295576 eq16
    | (have j1 := eq295576 X0
       grind)
    | exact resolve eq16 eq295576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295576
  have eq312495 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq312413 X0
       have i₂ := eq298751
       grind)
    | exact superpose eq298751 eq312413
    | (have j0 := eq312413 X0
       grind)
    | exact resolve eq312413 eq298751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312413
  have eq312496 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq312495 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312495
  have eq312675 : ∀ X0 : G, (σ (σ x)) = (M.op (σ (σ x)) (M.op (M.op X0 (σ (σ x))) (σ (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq66707 (σ x) X0
       have i₂ := eq312496 (σ x)
       grind)
    | exact superpose eq312496 eq66707
    | exact resolve eq66707 eq312496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66707
  have eq312677 : ∀ X0 : G, (M.op X0 (M.op (τ (σ x)) (M.op X0 (τ (σ x))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq68249 (σ x) X0
       have i₂ := eq312496 (σ x)
       grind)
    | exact superpose eq312496 eq68249
    | exact resolve eq68249 eq312496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68249
  have eq312681 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ x)) (M.op (M.op X0 (τ (σ x))) (τ (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq68379 (σ x) X0
       have i₂ := eq312496 (σ x)
       grind)
    | exact superpose eq312496 eq68379
    | exact resolve eq68379 eq312496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68379
  have eq312710 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (σ x) X0
       have i₂ := eq312496 (σ X0)
       grind)
    | exact superpose eq312496 eq24
    | exact resolve eq24 eq312496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq312496
  have eq312810 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq312710 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq312710
    | exact resolve eq312710 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312710
  have eq312817 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ x)) (M.op X0 (τ (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq312681 X0
       have i₂ := eq780 (τ (σ x)) X0
       grind)
    | exact superpose eq780 eq312681
    | exact resolve eq312681 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312681
  have eq312821 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq312677 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq312677
    | exact resolve eq312677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312677
  have eq312823 : ∀ X0 : G, (σ (σ x)) = (M.op (σ (σ x)) (M.op X0 (σ (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq312675 X0
       have i₂ := eq780 (σ (σ x)) X0
       grind)
    | exact superpose eq780 eq312675
    | exact resolve eq312675 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq312675
  have eq312855 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq312817 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq312817
    | exact resolve eq312817 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312817
  have eq313085 : ∀ X0 : G, (k X0 (σ (σ (M.op x (M.op (τ (τ X0)) x))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq64790 x X0
       have i₂ := eq312810 x
       grind)
    | exact superpose eq312810 eq64790
    | exact resolve eq64790 eq312810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312810
  have eq313347 : ∀ X0 : G, (k X0 (σ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq313085 X0
       have i₂ := eq312855 (τ (τ X0))
       grind)
    | exact superpose eq312855 eq313085
    | exact resolve eq313085 eq312855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313085
  have eq317137 : ∀ X0 : G, (k X0 (σ (σ (M.op (σ (σ x)) (M.op (τ (τ X0)) (σ (σ x))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq64790 (σ (σ x)) X0
       have i₂ := eq313347 (σ (σ x))
       grind)
    | exact superpose eq313347 eq64790
    | exact resolve eq64790 eq313347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64790 eq313347
  have eq317303 : ∀ X0 : G, (k X0 (σ (σ (σ (σ x))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq317137 X0
       have i₂ := eq312823 (τ (τ X0))
       grind)
    | exact superpose eq312823 eq317137
    | exact resolve eq317137 eq312823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312823 eq317137
  have eq320526 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq312821 X0
       have i₂ := eq312855 X0
       grind)
    | exact superpose eq312855 eq312821
    | exact resolve eq312821 eq312855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320719 : ∀ X0 X1 : G, (M.op X1 (M.op x (M.op X0 x))) = (M.op (M.op X1 (M.op x (M.op X0 x))) (M.op X0 (M.op X1 (M.op x (M.op X0 x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq894 X1 (M.op x (M.op X0 x)) X0
       have i₂ := eq312821 X0
       grind)
    | exact superpose eq312821 eq894
    | exact resolve eq894 eq312821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq312821
  have eq320880 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X1 x) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq320719 X0 X1
       have i₂ := eq312855 X0
       grind)
    | exact superpose eq312855 eq320719
    | exact resolve eq320719 eq312855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312855 eq320719
  have eq320955 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq320880 X0 X0
       have i₂ := eq320526 X0
       grind)
    | exact superpose eq320526 eq320880
    | exact resolve eq320880 eq320526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320526 eq320880
  have eq331346 : ∀ X0 : G, (M.op X0 (M.op (τ (τ (σ (σ (σ (σ x)))))) (M.op X0 (τ (τ (σ (σ (σ (σ x))))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq84534 (σ (σ (σ (σ x)))) X0
       have i₂ := eq317303 (σ (σ (σ (σ x))))
       grind)
    | exact superpose eq317303 eq84534
    | exact resolve eq84534 eq317303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84534 eq317303
  have eq331446 : ∀ X0 : G, (M.op X0 (τ (τ (σ (σ (σ (σ x))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq331346 X0
       have i₂ := eq320955 X0 (τ (τ (σ (σ (σ (σ x))))))
       grind)
    | exact superpose eq320955 eq331346
    | exact resolve eq331346 eq320955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331346
  have eq331492 : ∀ X0 : G, (M.op X0 (τ (σ (σ (σ x))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq331446 X0
       have i₂ := eq10 (σ (σ (σ x)))
       grind)
    | exact superpose eq10 eq331446
    | exact resolve eq331446 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331446
  have eq331506 : ∀ X0 : G, (M.op X0 (σ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq331492 X0
       have i₂ := eq10 (σ (σ x))
       grind)
    | exact superpose eq10 eq331492
    | exact resolve eq331492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331492
  have eq331583 : ∀ X0 : G, (M.op X0 (M.op (τ (σ (σ x))) (M.op X0 (τ (σ (σ x)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq280406 (σ (σ x)) X0
       have i₂ := eq331506 (σ (σ x))
       grind)
    | exact superpose eq331506 eq280406
    | exact resolve eq280406 eq331506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280406 eq331506
  have eq332021 : ∀ X0 : G, (M.op X0 (τ (σ (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq331583 X0
       have i₂ := eq320955 X0 (τ (σ (σ x)))
       grind)
    | exact superpose eq320955 eq331583
    | exact resolve eq331583 eq320955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331583
  have eq332041 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq332021 X0
       have i₂ := eq10 (σ x)
       grind)
    | exact superpose eq10 eq332021
    | exact resolve eq332021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332021
  have eq332295 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq320955 X0 (σ x)
       have i₂ := eq332041 X0
       grind)
    | exact superpose eq332041 eq320955
    | exact resolve eq320955 eq332041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320955 eq332041
  have eq332602 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq332295 (σ y)
       grind)
    | exact superpose eq332295 eq16
    | exact resolve eq16 eq332295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332295
  have eq333734 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq332602
       have i₂ := eq298751
       grind)
    | exact superpose eq298751 eq332602
    | exact resolve eq332602 eq298751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298751 eq332602
  have eq333735 : False := by grind
  exact eq333735

/-- `Equation882`: `x = y ◇ ((x ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation882 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law882 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law882.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq61 (σ X1) (σ X0)
       grind)
    | exact superpose eq61 eq15
    | (have j1 := eq61 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq61 (τ X1) X0
       grind)
    | exact superpose eq61 eq18
    | (have j1 := eq61 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq61
  have eq292 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq67
    | exact resolve eq67 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq310 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq292
    | (have j0 := eq292 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq846 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq884 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq846
       have i₂ := eq310 y x
       grind)
    | exact superpose eq310 eq846
    | (have j1 := eq310 (σ x) (σ y)
       grind)
    | (have r₁ := eq846
       have r₂ := eq310 y x
       grind)
    | (have r₁ := eq846
       have r₂ := eq310 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq846
       have r₂ := eq310 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq846 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310 eq846
  have eq885 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq884
  have eq999 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq885
       grind)
    | exact superpose eq885 eq10
    | exact resolve eq10 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1035 : x = y ∨ x = y := by
    first
    | (have i₁ := eq999
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq999
    | exact resolve eq999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1036 : x = y := by grind
  clear eq1035
  have eq1151 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1036
       grind)
    | exact superpose eq1036 eq16
    | exact resolve eq16 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1152 : False := by grind
  exact eq1152

/-- `Equation887`: `x = y ◇ ((x ◇ y) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_x_x_pxy_Equation887 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law887 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (M.op X0 X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X1
       have i₂ := eq21 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) X2
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X1) X0 X1
       have i₂ := eq23 (M.op X1 X1) X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq46 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq51 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq51 X1 X0
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq51 (k X1 X0) X1
       grind)
    | (have r₁ := eq42 X0 X0
       have r₂ := eq51 X0 (k X0 X0)
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq51 X0 X1
       grind)
    | exact resolve eq42 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq51
  have eq58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq54 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq70 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X0 X0) X1
       have i₂ := eq25 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq25 eq23
    | exact resolve eq23 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq58 (τ X1) X0
       grind)
    | exact superpose eq58 eq19
    | (have j1 := eq58 (τ X1) X0
       grind)
    | exact resolve eq19 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq156 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq302 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq156 X0 (M.op X1 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq156
    | (have j0 := eq156 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq156 X0 (M.op X1 X1)
       have r₂ := eq25 X0 X1
       grind)
    | exact resolve eq156 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq385 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 (M.op X1 X1)
       have i₂ := eq311 (σ X0) X1
       grind)
    | exact superpose eq311 eq120
    | exact resolve eq120 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq311
  have eq388 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq385
    | exact resolve eq385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq1759 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq154
    | exact resolve eq154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq1811 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1759 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1759
    | (have j0 := eq1759 X0 X1
       grind)
    | exact resolve eq1759 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq1917 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq46 (τ (M.op X1 X1)) X0
       grind)
    | exact superpose eq46 eq388
    | (have j1 := eq46 (τ (M.op X1 X1)) X0
       grind)
    | exact resolve eq388 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq1978 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1917 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq2105 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq151 x y
       grind)
    | exact superpose eq151 eq16
    | (have j1 := eq151 x y
       grind)
    | exact resolve eq16 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq3350 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1978 (τ (M.op X1 X1)) X1
       have i₂ := eq31 (τ (M.op X1 X1)) X1
       grind)
    | (have i₁ := eq1978 (τ (M.op X1 X1)) X1
       have i₂ := eq31 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq31 eq1978
    | exact resolve eq1978 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978
  have eq3445 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq3706 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1)
       have i₂ := eq3445 X0 X1
       grind)
    | exact superpose eq3445 eq11
    | exact resolve eq11 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4860 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X1
       have i₂ := eq3706 X0 X1
       grind)
    | exact superpose eq3706 eq23
    | exact resolve eq23 eq3706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155334 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2105
       have i₂ := eq1811 y x
       grind)
    | exact superpose eq1811 eq2105
    | (have j1 := eq1811 y x
       grind)
    | (have r₁ := eq2105
       have r₂ := eq1811 y x
       grind)
    | exact resolve eq2105 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811 eq2105
  have eq155335 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by grind
  clear eq155334
  have eq155337 : (M.op x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq155335
       grind)
    | exact superpose eq155335 eq10
    | exact resolve eq10 eq155335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155335
  have eq155371 : x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq155337
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq155337
    | exact resolve eq155337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155337
  have eq155372 : x = (k x y) := by
    first
    | (have j1 := eq156 x y
       grind)
    | (have r₁ := eq155371
       have r₂ := eq156 x y
       grind)
    | exact resolve eq155371 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq155371
  have eq155571 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46 y x
       have i₂ := eq155372
       grind)
    | exact superpose eq155372 eq46
    | (have j0 := eq46 y x
       grind)
    | exact resolve eq46 eq155372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq155372
  have eq155580 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq155571
  have eq156231 : ∀ X0 X1 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op x (M.op X1 X1))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq20 x y X0 X1
       have i₂ := eq155580
       grind)
    | exact superpose eq155580 eq20
    | exact resolve eq20 eq155580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq156233 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23 x y
       have i₂ := eq155580
       grind)
    | exact superpose eq155580 eq23
    | exact resolve eq23 eq155580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq155580
  have eq156248 : ∀ X0 : G, (M.op X0 X0) = y ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq156231 X0 x
       have i₂ := eq26 x (M.op X0 X0) x
       grind)
    | exact superpose eq26 eq156231
    | exact resolve eq156231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq156231
  have eq157227 : ∀ X0 : G, (M.op X0 X0) = y ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq156233
       have i₂ := eq31 x x
       grind)
    | (have i₁ := eq156233
       have i₂ := eq31 X0 x
       grind)
    | exact superpose eq31 eq156233
    | exact resolve eq156233 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq157237 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq70 x X0
       have i₂ := eq156233
       grind)
    | exact superpose eq156233 eq70
    | exact resolve eq70 eq156233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157268 : ∀ X0 : G, (M.op X0 X0) = (τ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq3445 X0 x
       have i₂ := eq156233
       grind)
    | exact superpose eq156233 eq3445
    | exact resolve eq3445 eq156233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445 eq156233
  have eq158443 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70 x X0
       have i₂ := eq156248 X1
       grind)
    | exact superpose eq156248 eq70
    | (have j1 := eq156248 X1
       grind)
    | exact resolve eq70 eq156248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158489 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4860 x X0
       have i₂ := eq156248 X1
       grind)
    | exact superpose eq156248 eq4860
    | (have j1 := eq156248 X1
       grind)
    | exact resolve eq4860 eq156248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156248
  have eq158930 : ∀ X0 X1 : G, (M.op X0 y) = X0 ∨ x = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq157227 X1
       grind)
    | exact superpose eq157227 eq25
    | (have j1 := eq157227 X1
       grind)
    | exact resolve eq25 eq157227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq157227
  have eq171937 : y = (τ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq157237 y
       have i₂ := eq157268 y
       grind)
    | exact superpose eq157268 eq157237
    | exact resolve eq157237 eq157268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157237 eq157268
  have eq172090 : x = (M.op x x) ∨ y = (τ y) := by grind
  clear eq171937
  have eq172210 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq70 x X0
       have i₂ := eq172090
       grind)
    | exact superpose eq172090 eq70
    | exact resolve eq70 eq172090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq172256 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq4860 x X0
       have i₂ := eq172090
       grind)
    | exact superpose eq172090 eq4860
    | exact resolve eq4860 eq172090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4860 eq172090
  have eq175606 : (σ (M.op x y)) ≠ (σ y) ∨ y = (τ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq172256 (σ y)
       grind)
    | exact superpose eq172256 eq16
    | exact resolve eq16 eq172256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172256
  have eq262088 : (σ y) ≠ (σ y) ∨ y = (τ y) ∨ y = (τ y) := by
    first
    | (have i₁ := eq175606
       have i₂ := eq172210 y
       grind)
    | exact superpose eq172210 eq175606
    | exact resolve eq175606 eq172210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172210 eq175606
  have eq262094 : (σ y) ≠ (σ y) ∨ y = (τ y) := by grind
  clear eq262088
  have eq262095 : y = (τ y) := by grind
  clear eq262094
  have eq262149 : y = (σ y) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq262095
       grind)
    | exact superpose eq262095 eq11
    | exact resolve eq11 eq262095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262095
  have eq262159 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262149
       grind)
    | exact superpose eq262149 eq16
    | exact resolve eq16 eq262149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263396 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq262159
       have i₂ := eq158930 x X0
       grind)
    | exact superpose eq158930 eq262159
    | (have j1 := eq158930 X0 X0
       grind)
    | exact resolve eq262159 eq158930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263405 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq262159
       have i₂ := eq158443 y X0
       grind)
    | exact superpose eq158443 eq262159
    | (have j1 := eq158443 X0 X0
       grind)
    | exact resolve eq262159 eq158443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158443 eq262159
  have eq263417 : ∀ X0 : G, y ≠ (M.op (σ x) y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq263405 X0
       have i₂ := eq262149
       grind)
    | exact superpose eq262149 eq263405
    | (have j0 := eq263405 X0
       grind)
    | exact resolve eq263405 eq262149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262149 eq263405
  have eq263426 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq263396 X0
       have j1 := eq158930 X0 X0
       grind)
    | (have r₁ := eq263396 X0
       have r₂ := eq158930 (σ x) x
       grind)
    | exact resolve eq263396 eq158930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158930 eq263396
  have eq263433 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq263417 X0
       have j1 := eq158489 X0 X0
       grind)
    | (have r₁ := eq263417 X0
       have r₂ := eq158489 y x
       grind)
    | exact resolve eq263417 eq158489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158489 eq263417
  have eq263439 : x = y := by
    first
    | (have i₁ := eq263433 x
       have i₂ := eq263426 x
       grind)
    | exact superpose eq263426 eq263433
    | exact resolve eq263433 eq263426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263426 eq263433
  have eq263443 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq263439
       grind)
    | exact superpose eq263439 eq16
    | exact resolve eq16 eq263439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263439
  have eq263712 : False := by grind
  exact eq263712

/-- `Equation887`: `x = y ◇ ((x ◇ y) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_x_x_pyx_Equation887 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law887 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (M.op X0 X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X1
       have i₂ := eq21 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X1) X0 X1
       have i₂ := eq23 (M.op X1 X1) X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq44 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 X2) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X1 X2) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq44 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq44 (k X0 X1) X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 (k X0 X1) X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 (M.op X0 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq54 X0 X1 X0
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq54 (k X1 X0) X1 x
       grind)
    | (have r₁ := eq55 X0 X0
       have r₂ := eq54 X0 (k X0 X0) x
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq54 X0 X1 x
       grind)
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq55
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq25 (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq25 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X0 X0) X1
       have i₂ := eq25 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq25 eq23
    | exact resolve eq23 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq153 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq59 (τ X0) X1
       grind)
    | exact superpose eq59 eq19
    | (have j1 := eq59 (τ X0) X1
       grind)
    | exact resolve eq19 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq59 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X0
       have i₂ := eq31 (σ X0) X1
       grind)
    | (have i₁ := eq49 X0 X0
       have i₂ := eq31 X0 (σ X0)
       grind)
    | exact superpose eq31 eq49
    | exact resolve eq49 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq982 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq830 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq2100 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq156 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq156
    | exact resolve eq156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq2158 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2100 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2100
    | (have j0 := eq2100 X0 X1
       grind)
    | exact resolve eq2100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq2582 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq153 y x
       grind)
    | exact superpose eq153 eq16
    | (have j1 := eq153 y x
       grind)
    | exact resolve eq16 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq6040 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq982 X1 (M.op X0 X0)
       have i₂ := eq72 X0 (M.op X0 X0)
       grind)
    | exact superpose eq72 eq982
    | (have j0 := eq982 X1 (M.op X0 X0)
       grind)
    | exact resolve eq982 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq6143 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X1)
       have i₂ := eq982 X0 (τ X1)
       grind)
    | exact superpose eq982 eq19
    | (have j1 := eq982 X0 (τ X1)
       grind)
    | exact resolve eq19 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq982
  have eq6176 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6040 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6040
  have eq6210 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6143 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6143
    | (have j0 := eq6143 X0 X1
       grind)
    | exact resolve eq6143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6143
  have eq6250 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6210 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6210
    | (have j0 := eq6210 X0 X1
       grind)
    | exact resolve eq6210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6210
  have eq6739 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X1
       have i₂ := eq6176 X0 X1
       grind)
    | exact superpose eq6176 eq23
    | exact resolve eq23 eq6176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq47277 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6250
  have eq48737 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47277 X1 X0
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq47277
    | (have j0 := eq47277 X1 X0
       have j1 := eq59 X0 X0
       grind)
    | (have r₁ := eq47277 X0 X0
       have r₂ := eq59 X0 X0
       grind)
    | exact resolve eq47277 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq48845 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48737 X0 X1
       have j1 := eq47277 X1 X0
       grind)
    | (have r₁ := eq48737 X1 X1
       have r₂ := eq47277 X1 X1
       grind)
    | (have r₁ := eq48737 (M.op X0 X0) X1
       have r₂ := eq47277 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq48737 (k (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq47277 X0 (M.op X1 X1)
       grind)
    | exact resolve eq48737 eq47277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47277 eq48737
  have eq143636 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2582
       have i₂ := eq2158 x y
       grind)
    | exact superpose eq2158 eq2582
    | (have j1 := eq2158 x y
       grind)
    | (have r₁ := eq2582
       have r₂ := eq2158 x y
       grind)
    | exact resolve eq2582 eq2158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158 eq2582
  have eq143637 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq143636
  have eq143639 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq143637
       grind)
    | exact superpose eq143637 eq10
    | exact resolve eq10 eq143637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143637
  have eq143673 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq143639
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq143639
    | exact resolve eq143639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143639
  have eq143674 : y = (k y x) := by
    first
    | (have j1 := eq158 y x
       grind)
    | (have r₁ := eq143673
       have r₂ := eq158 y x
       grind)
    | exact resolve eq143673 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq143673
  have eq147031 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq143674
       have i₂ := eq45 x y
       grind)
    | exact superpose eq45 eq143674
    | (have j1 := eq45 x y
       grind)
    | exact resolve eq143674 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq143674
  have eq147185 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq147031
  have eq147317 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25 X0 y
       have i₂ := eq147185
       grind)
    | exact superpose eq147185 eq25
    | exact resolve eq25 eq147185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq147321 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq71 y X0
       have i₂ := eq147185
       grind)
    | exact superpose eq147185 eq71
    | exact resolve eq71 eq147185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147344 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6176 y X0
       have i₂ := eq147185
       grind)
    | exact superpose eq147185 eq6176
    | exact resolve eq6176 eq147185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147406 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq48845 y X0
       have i₂ := eq147185
       grind)
    | exact superpose eq147185 eq48845
    | (have j0 := eq48845 y X0
       grind)
    | (have r₁ := eq48845 y x
       have r₂ := eq147185
       grind)
    | exact resolve eq48845 eq147185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48845 eq147185
  have eq147433 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq147406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147406
  have eq148160 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 x y
       have i₂ := eq147317 X0
       grind)
    | exact superpose eq147317 eq21
    | (have j1 := eq147317 X0
       grind)
    | exact resolve eq21 eq147317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147317
  have eq150231 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq21 x y
       have i₂ := eq147433 X0
       grind)
    | exact superpose eq147433 eq21
    | (have j1 := eq147433 X0
       grind)
    | exact resolve eq21 eq147433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147433
  have eq150876 : ∀ X0 X1 : G, (M.op X0 X0) = x ∨ (M.op X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 y
       have i₂ := eq148160 X1
       grind)
    | exact superpose eq148160 eq31
    | (have j1 := eq148160 X1
       grind)
    | exact resolve eq31 eq148160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq148160
  have eq152100 : ∀ X0 X1 : G, (M.op x X0) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq71 y X0
       have i₂ := eq150231 X1
       grind)
    | exact superpose eq150231 eq71
    | (have j1 := eq150231 X1
       grind)
    | exact resolve eq71 eq150231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152134 : ∀ X0 X1 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6739 y X0
       have i₂ := eq150231 X1
       grind)
    | exact superpose eq150231 eq6739
    | (have j1 := eq150231 X1
       grind)
    | exact resolve eq6739 eq150231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150231
  have eq165894 : y = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq147321 y
       have i₂ := eq147344 y
       grind)
    | exact superpose eq147344 eq147321
    | exact resolve eq147321 eq147344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147321 eq147344
  have eq165911 : y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq165894
  have eq166056 : x = (M.op y y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq21 x y
       have i₂ := eq165911
       grind)
    | exact superpose eq165911 eq21
    | exact resolve eq21 eq165911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq165911
  have eq166126 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq71 y X0
       have i₂ := eq166056
       grind)
    | exact superpose eq166056 eq71
    | exact resolve eq71 eq166056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq166160 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6739 y X0
       have i₂ := eq166056
       grind)
    | exact superpose eq166056 eq6739
    | exact resolve eq6739 eq166056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6739 eq166056
  have eq168871 : (σ (M.op x y)) ≠ (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq166160 (σ y)
       grind)
    | exact superpose eq166160 eq16
    | exact resolve eq16 eq166160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166160
  have eq257833 : (σ y) ≠ (σ y) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq168871
       have i₂ := eq166126 y
       grind)
    | exact superpose eq166126 eq168871
    | exact resolve eq168871 eq166126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166126 eq168871
  have eq257840 : (σ y) ≠ (σ y) ∨ y = (σ y) := by grind
  clear eq257833
  have eq257841 : y = (σ y) := by grind
  clear eq257840
  have eq257855 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq257841
       grind)
    | exact superpose eq257841 eq16
    | exact resolve eq16 eq257841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258128 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq257855
       have i₂ := eq150876 X0 x
       grind)
    | exact superpose eq150876 eq257855
    | (have j1 := eq150876 X0 x
       grind)
    | exact resolve eq257855 eq150876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258136 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq257855
       have i₂ := eq152100 y X0
       grind)
    | exact superpose eq152100 eq257855
    | (have j1 := eq152100 X0 X0
       grind)
    | exact resolve eq257855 eq152100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152100 eq257855
  have eq258146 : ∀ X0 : G, y ≠ (M.op (σ x) y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq258136 X0
       have i₂ := eq257841
       grind)
    | exact superpose eq257841 eq258136
    | (have j0 := eq258136 X0
       grind)
    | exact resolve eq258136 eq257841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257841 eq258136
  have eq258154 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq258128 X0
       have j1 := eq150876 X0 x
       grind)
    | (have r₁ := eq258128 X0
       have r₂ := eq150876 X0 (σ x)
       grind)
    | exact resolve eq258128 eq150876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150876 eq258128
  have eq258164 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq258146 X0
       have j1 := eq152134 X0 X0
       grind)
    | (have r₁ := eq258146 X0
       have r₂ := eq152134 y x
       grind)
    | exact resolve eq258146 eq152134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152134 eq258146
  have eq258176 : x = y := by
    first
    | (have i₁ := eq258164 x
       have i₂ := eq258154 x
       grind)
    | exact superpose eq258154 eq258164
    | exact resolve eq258164 eq258154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258154 eq258164
  have eq258187 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq258176
       grind)
    | exact superpose eq258176 eq16
    | exact resolve eq16 eq258176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258176
  have eq258484 : False := by grind
  exact eq258484
