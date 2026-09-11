import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4440`: `x ◇ (y ◇ x) = (x ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pxy_x_pxy_Equation4440 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4440 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4440.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X2) := by
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X0 x X3
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) y) := by
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
  have eq56 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
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
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq95
    | (have j0 := eq95 X0 (σ X1)
       grind)
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq44
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq44 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq147 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq43
  have eq204 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op x (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq55 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 sF2)
       have i₂ := eq14 X0 X1 sF2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq56 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq303 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq353 : (M.op (M.op x y) y) = (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq55 (M.op x x)
       have i₂ := eq205 x
       grind)
    | exact superpose eq205 eq55
    | exact resolve eq55 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq473 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X0 X2) X3
       have i₂ := eq52 X0 X2 X1
       grind)
    | (have i₁ := eq14 X2 (M.op X0 X2) X3
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 sF2)
       have i₂ := eq52 X0 sF2 x
       grind)
    | (have i₁ := eq56 (M.op X0 sF2)
       have i₂ := eq52 X0 X1 sF2
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq511 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq303
    | exact resolve eq303 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq553 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X2 (M.op X0 X2) X3
       have i₂ := eq52 X0 X2 X1
       grind)
    | (have i₁ := eq57 X2 (M.op X0 X2) X3
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq57 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57
    | (have j0 := eq57 y x X0
       grind)
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq689 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51
    | (have j0 := eq51 y x X0 X1
       grind)
    | exact resolve eq51 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1539 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (M.op (σ X0) X2) X2) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ X0) (σ X1) X2
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq52
    | (have j1 := eq99 X0 X1
       grind)
    | exact resolve eq52 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1549 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq99 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq119 eq95
    | (have j0 := eq95 x (σ y)
       grind)
    | exact resolve eq95 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1687
    | exact resolve eq1687 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq1691 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1688
       have r₂ := eq27
       grind)
    | exact resolve eq1688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1696 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1691 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1691
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1691
       grind)
    | exact resolve eq13 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1709 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1696
  have eq1795 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1709 eq89
    | exact resolve eq89 eq1709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1709
  have eq1799 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1795
    | exact resolve eq1795 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1795
  have eq1802 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq95 y y
       have i₂ := eq1799
       grind)
    | exact superpose eq1799 eq95
    | (have j0 := eq95 x y
       grind)
    | exact resolve eq95 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq1803 : y = (M.op y y) := by grind
  clear eq1802
  have eq1885 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq558 y
       have i₂ := eq1803
       grind)
    | exact superpose eq1803 eq558
    | exact resolve eq558 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq1887 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1803
       grind)
    | exact superpose eq1803 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1803
       grind)
    | exact resolve eq13 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1901 : (M.op (M.op x y) y) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq204 y y
       have i₂ := eq1803
       grind)
    | exact superpose eq1803 eq204
    | exact resolve eq204 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1902 : y = (k y y) := by grind
  clear eq1887
  have eq1904 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1901
       have i₂ := eq1803
       grind)
    | exact superpose eq1803 eq1901
    | exact resolve eq1901 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq1918 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1885
       have i₂ := eq1803
       grind)
    | exact superpose eq1803 eq1885
    | exact resolve eq1885 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803 eq1885
  have eq1920 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1904
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1904
    | exact resolve eq1904 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq1930 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq1902
       grind)
    | exact superpose eq1902 eq78
    | exact resolve eq78 eq1902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1902
  have eq1934 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1930
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1930
    | exact resolve eq1930 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1930
  have eq2004 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1920 eq353
    | exact resolve eq353 eq1920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq2184 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1934 eq95
    | (have j0 := eq95 x (σ y)
       grind)
    | exact resolve eq95 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934
  have eq2185 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2184
  have eq2189 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2004 eq205
    | exact resolve eq205 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq2004
  have eq2213 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1920 eq2189
    | exact resolve eq2189 eq1920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920 eq2189
  have eq2237 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq2185 eq211
    | exact resolve eq211 eq2185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq2240 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2185 eq2237
    | exact resolve eq2237 eq2185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185 eq2237
  have eq2257 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq2240
    | exact resolve eq2240 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2240
  have eq2430 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2213 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq2213
       grind)
    | exact resolve eq13 eq2213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2447 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq2430
  have eq2715 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2447 eq129
    | exact resolve eq129 eq2447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq2447
  have eq2719 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2715
    | exact resolve eq2715 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2715
  have eq2917 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 y) := by
    intro X0 X1
    first
    | exact superpose eq1918 eq689
    | exact resolve eq689 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq1918
  have eq3040 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq212 x
       have i₂ := eq2917 sF2 x
       grind)
    | exact superpose eq2917 eq212
    | (have j1 := eq2917 (σ x) (σ y)
       grind)
    | exact resolve eq212 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq3110 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq2257 eq3040
    | exact resolve eq3040 eq2257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3791 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2719 eq95
    | (have j0 := eq95 x (σ (M.op x y))
       grind)
    | exact resolve eq95 eq2719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq2719
  have eq3792 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3791
  have eq3823 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3792 eq475
    | exact resolve eq475 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq3830 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3792 eq3823
    | exact resolve eq3823 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3823
  have eq3845 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2257 eq3830
    | exact resolve eq3830 eq2257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257 eq3830
  have eq3855 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X2 (M.op X0 y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq473 X0 x X2 X3
       have i₂ := eq2917 X0 x
       grind)
    | exact superpose eq2917 eq473
    | exact resolve eq473 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq3856 : ∀ X0 X2 : G, (M.op X2 y) = (M.op X2 (M.op X0 y)) := by
    intro X0 X2
    first
    | (have i₁ := eq3855 X0 X2 x
       have i₂ := eq2917 X2 x
       grind)
    | exact superpose eq2917 eq3855
    | exact resolve eq3855 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3855
  have eq4272 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X2 (M.op X0 y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq553 X0 x X2 X3
       have i₂ := eq2917 X0 x
       grind)
    | exact superpose eq2917 eq553
    | exact resolve eq553 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq4273 : ∀ X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X2 y) := by
    intro X2 X3
    first
    | (have i₁ := eq4272 x X2 X3
       have i₂ := eq3856 x X2
       grind)
    | exact superpose eq3856 eq4272
    | exact resolve eq4272 eq3856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3856 eq4272
  have eq12281 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1549 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1549
    | (have j0 := eq1549 (τ X0)
       grind)
    | exact resolve eq1549 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq12294 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12281 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12281
    | (have j0 := eq12281 X0
       grind)
    | exact resolve eq12281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12281
  have eq12301 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12294 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12294
    | (have j0 := eq12294 X0
       grind)
    | exact resolve eq12294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12294
  have eq29211 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (σ X0) y) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1539 X0 X1 x
       have i₂ := eq2917 (σ X0) x
       grind)
    | exact superpose eq2917 eq1539
    | (have j0 := eq1539 X0 X1 x
       grind)
    | exact resolve eq1539 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539 eq2917
  have eq29727 : ∀ X0 X1 : G, (M.op (σ X0) y) = (σ (k (k X0 X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (k X0 X1) X1
       have i₂ := eq29211 X0 X1
       grind)
    | exact superpose eq29211 eq99
    | (have j0 := eq99 X0 X1
       have j1 := eq29211 X0 X1
       grind)
    | exact resolve eq99 eq29211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq29211
  have eq29761 : ∀ X0 X1 : G, (M.op (σ X0) y) = (σ (k (k X0 X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq29727 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29727
  have eq184645 : ∀ X0 : G, (M.op (σ x) y) = (σ (k (τ (k (σ x) X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq29761 x (τ X0)
       have i₂ := eq234 X0
       grind)
    | exact superpose eq234 eq29761
    | (have j0 := eq29761 X0 (τ X0)
       grind)
    | exact resolve eq29761 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq185287 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq184645 X0
       have i₂ := eq34 (k sF2 X0) (τ X0)
       grind)
    | exact superpose eq34 eq184645
    | (have j0 := eq184645 X0
       grind)
    | exact resolve eq184645 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184645
  have eq185523 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq185287 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq185287
    | (have j0 := eq185287 X0
       grind)
    | exact resolve eq185287 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185287
  have eq185650 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq185523 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq185523
    | (have j0 := eq185523 X0
       grind)
    | exact resolve eq185523 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185523
  have eq185677 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq3110 eq185650
    | (have j0 := eq185650 X0
       grind)
    | exact resolve eq185650 eq3110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110 eq185650
  have eq185695 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ x) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq185677 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq185677
    | (have j0 := eq185677 X0
       grind)
    | exact resolve eq185677 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185677
  have eq2043509 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29761 (τ X0) (τ X1)
       have i₂ := eq511 X1 X0
       grind)
    | exact superpose eq511 eq29761
    | (have j0 := eq29761 X0 (τ X1)
       grind)
    | exact resolve eq29761 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq29761
  have eq2043744 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (k (k X0 X1) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2043509 X0 X1
       have i₂ := eq34 (k X0 X1) (τ X1)
       grind)
    | exact superpose eq34 eq2043509
    | (have j0 := eq2043509 X0 X1
       grind)
    | exact resolve eq2043509 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq2043509
  have eq2044203 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op (σ (τ X0)) y) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2043744 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq2043744
    | (have j0 := eq2043744 X0 X1
       grind)
    | exact resolve eq2043744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043744
  have eq2044578 : ∀ X0 X1 : G, (M.op X0 y) = (k (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2044203 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2044203
    | (have j0 := eq2044203 X0 X1
       grind)
    | exact resolve eq2044203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044203
  have eq2044874 : ∀ X0 X1 : G, (M.op X0 y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2044578 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2044578
    | (have j0 := eq2044578 X0 X1
       grind)
    | exact resolve eq2044578 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044578
  have eq3912124 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq147
       have i₂ := eq2044874 x x
       grind)
    | exact superpose eq2044874 eq147
    | (have j1 := eq2044874 x x
       grind)
    | exact resolve eq147 eq2044874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq2044874
  have eq3912402 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3912124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3912124
    | exact resolve eq3912124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912124
  have eq3914123 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3912402
    | exact resolve eq3912402 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912402
  have eq3952472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3914123 eq185695
    | (have j0 := eq185695 (σ x)
       grind)
    | exact resolve eq185695 eq3914123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185695 eq3914123
  have eq3952723 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq3952472
       have r₂ := eq27
       grind)
    | exact resolve eq3952472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3952472
  have eq3952929 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3952723 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq3952723
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq3952723
       grind)
    | exact resolve eq13 eq3952723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3952723
  have eq3953006 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq3952929
  have eq3953682 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3953006 eq49
    | exact resolve eq49 eq3953006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3953006
  have eq3953961 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq3953682
    | exact resolve eq3953682 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3953682
  have eq3953968 : x = (M.op x x) := by
    first
    | (have j1 := eq12301 x
       grind)
    | (have r₁ := eq3953961
       have r₂ := eq12301 x
       grind)
    | exact resolve eq3953961 eq12301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12301 eq3953961
  have eq3954029 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4273 x x
       have i₂ := eq3953968
       grind)
    | exact superpose eq3953968 eq4273
    | exact resolve eq4273 eq3953968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273
  have eq3954132 : x = (M.op x y) := by
    first
    | (have i₁ := eq3954029
       have i₂ := eq3953968
       grind)
    | exact superpose eq3953968 eq3954029
    | exact resolve eq3954029 eq3953968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953968 eq3954029
  have eq3954214 : x = (M.op x y) := by
    first
    | (have i₁ := eq3954132
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3954132
    | exact resolve eq3954132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3954132
  have eq3954352 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3954214 eq20
    | exact resolve eq20 eq3954214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3954214
  have eq3955591 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3954352
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3954352
    | exact resolve eq3954352 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3954352
  have eq3955669 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3955591 eq3845
    | exact resolve eq3845 eq3955591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845 eq3955591
  have eq3956831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3792 eq3955669
    | exact resolve eq3955669 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3792 eq3955669
  have eq3957055 : False := by grind
  exact eq3957055

/-- `Equation4454`: `x ◇ (y ◇ x) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_x_pxy_Equation4454 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4454 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4454.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) X2) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 (M.op X2 X1))) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X3 X1
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X2 X0) ∨ (k X2 (M.op X2 X0)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X2 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X2 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq83 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq115 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq108
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq217 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op y (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op y X0)
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (M.op (M.op x y) x) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ x)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq56 x
       have i₂ := eq14 sF3 x x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq228 eq229
    | exact resolve eq229 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq396 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq367 eq56
    | exact resolve eq56 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq367
  have eq397 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq228 eq396
    | exact resolve eq396 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq396
  have eq531 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X2 (M.op X2 X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq638 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 y x X1 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51
    | (have j0 := eq51 y x X1 X0
       grind)
    | exact resolve eq51 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op y (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | exact superpose eq218 eq217
    | exact resolve eq217 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1418 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 (M.op X2 X1))) = (M.op (M.op X1 (M.op y (M.op x y))) X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq53 x X1 X2 X3
       have i₂ := eq638 x X1
       grind)
    | exact superpose eq638 eq53
    | exact resolve eq53 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1419 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X3 (M.op X2 X1))) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1418 x X2 X3
       have i₂ := eq638 x (M.op y sF0)
       grind)
    | exact superpose eq638 eq1418
    | exact resolve eq1418 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1590 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op X0 y)) = (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1)))) (M.op y (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op X1 (M.op X2 X1)) X3 y X0
       have i₂ := eq882 X1 X2
       grind)
    | exact superpose eq882 eq54
    | exact resolve eq54 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq1601 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1590 X0 x x x
       have i₂ := eq1419 (M.op x x) x x
       grind)
    | exact superpose eq1419 eq1590
    | exact resolve eq1590 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq1619 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1601 X0
       have i₂ := eq638 (M.op y sF0) (M.op y sF0)
       grind)
    | exact superpose eq638 eq1601
    | exact resolve eq1601 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1623 : (M.op (M.op x y) x) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq1619 x
       have i₂ := eq55 x
       grind)
    | exact superpose eq55 eq1619
    | exact resolve eq1619 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1619
  have eq1624 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) := by
    first
    | exact superpose eq218 eq1623
    | exact resolve eq1623 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq2698 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2699 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq99 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq2700 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2699 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699
  have eq3157 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) (M.op X0 (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1624 eq54
    | exact resolve eq54 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3177 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op y (M.op x y)) (M.op X0 (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1624 eq3157
    | exact resolve eq3157 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157
  have eq3184 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq3177 x X1
       have i₂ := eq1419 sF0 y x
       grind)
    | exact superpose eq1419 eq3177
    | exact resolve eq3177 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq3177
  have eq3186 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1624 eq3184
    | exact resolve eq3184 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3184
  have eq3227 : (M.op y (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq3186
    | (have j0 := eq3186 (σ y) (σ x)
       grind)
    | exact resolve eq3186 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3415 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op y (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq531 X0 X1 X2 x
       have i₂ := eq3186 X2 x
       grind)
    | (have i₁ := eq531 X0 X1 y x
       have i₂ := eq3186 X0 X1
       grind)
    | exact superpose eq3186 eq531
    | exact resolve eq531 eq3186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq3416 : ∀ X2 : G, (M.op y (M.op x y)) = (M.op X2 (M.op y (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq3415 x x X2
       have i₂ := eq3186 x x
       grind)
    | (have i₁ := eq3415 y x X2
       have i₂ := eq3186 x x
       grind)
    | exact superpose eq3186 eq3415
    | (have j0 := eq3415 y x X2
       grind)
    | exact resolve eq3415 eq3186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415
  have eq3459 : ∀ X0 X1 : G, (M.op y (M.op x y)) ≠ (M.op (M.op y (M.op x y)) (M.op X0 (M.op y (M.op x y)))) ∨ (M.op X1 X1) = (k X1 (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq3416 eq68
    | (have r₁ := eq68 (M.op x y) y y
       have r₂ := eq3416 (M.op x y)
       grind)
    | exact resolve eq68 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq3489 : ∀ X1 : G, (M.op X1 X1) = (k X1 (M.op y (M.op x y))) := by
    intro X1
    first
    | (have j0 := eq3459 x X1
       grind)
    | (have r₁ := eq3459 X1 X1
       have r₂ := eq3186 (M.op y (M.op x y)) X1
       grind)
    | exact resolve eq3459 eq3186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3459
  have eq3690 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op (k X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq638 X0 X0
       have i₂ := eq3489 X0
       grind)
    | exact superpose eq3489 eq638
    | exact resolve eq638 eq3489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3711 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (k X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq3416 eq3690
    | exact resolve eq3690 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690
  have eq9197 : (M.op y y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq16
    | exact resolve eq16 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq9228 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq93 eq9197
    | exact resolve eq9197 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9197
  have eq9231 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq9228
       have r₂ := eq13 y y
       grind)
    | exact resolve eq9228 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9228
  have eq9889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9889
    | exact resolve eq9889 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9889
  have eq9901 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq9890
       have r₂ := eq27
       grind)
    | exact resolve eq9890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9890
  have eq9903 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9901
    | exact resolve eq9901 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9901
  have eq9907 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9903 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9903
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9903
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9903
       grind)
    | exact resolve eq12 eq9903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9903
  have eq9930 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq9907
  have eq9950 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9930
    | exact resolve eq9930 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9930
  have eq9951 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq9950
  have eq10037 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9951 eq88
    | exact resolve eq88 eq9951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9951
  have eq10053 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq10037
    | exact resolve eq10037 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10037
  have eq10383 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq10053
       grind)
    | exact superpose eq10053 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq10053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10053
  have eq10384 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10383
  have eq10386 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10384
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10384
    | exact resolve eq10384 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10384
  have eq10387 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10386
  have eq10397 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq10387
       grind)
    | exact superpose eq10387 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10387
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10387
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq10387
       grind)
    | exact resolve eq12 eq10387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10402 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 x y X1 X0
       have i₂ := eq10387
       grind)
    | exact superpose eq10387 eq51
    | exact resolve eq51 eq10387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq10417 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3186 x y
       have i₂ := eq10387
       grind)
    | exact superpose eq10387 eq3186
    | exact resolve eq3186 eq10387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10387
  have eq10419 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10397
  have eq10420 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10417
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10417
    | exact resolve eq10417 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10417
  have eq10433 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq10402 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10402
    | (have j0 := eq10402 X0 X1
       grind)
    | exact resolve eq10402 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10402
  have eq10437 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10419
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10419
    | exact resolve eq10419 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10419
  have eq10438 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10437
  have eq10446 : ∀ X1 : G, (M.op X1 (M.op y (M.op x y))) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq10433 x X1
       have i₂ := eq638 x X1
       grind)
    | exact superpose eq638 eq10433
    | exact resolve eq10433 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10433
  have eq10449 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq3416 eq10446
    | exact resolve eq10446 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10446
  have eq10468 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10420 eq1624
    | exact resolve eq1624 eq10420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624 eq10420
  have eq10532 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq10438
       grind)
    | exact superpose eq10438 eq77
    | exact resolve eq77 eq10438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10438
  have eq10548 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10532
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10532
    | exact resolve eq10532 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10532
  have eq10552 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10468 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq10468
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10468
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10468
       grind)
    | exact resolve eq13 eq10468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10468
  have eq10573 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10552
  have eq10865 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10548 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10548
  have eq10866 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10865
  have eq10868 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10866
    | exact resolve eq10866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10866
  have eq10869 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10868
  have eq10894 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10573 eq2700
    | (have j0 := eq2700 (M.op x y)
       grind)
    | exact resolve eq2700 eq10573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700 eq10573
  have eq10897 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10894
  have eq10900 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10897
    | exact resolve eq10897 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10897
  have eq10929 : (M.op (σ x) (σ y)) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10869 eq3186
    | exact resolve eq3186 eq10869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10869
  have eq10932 : (M.op (σ x) (σ y)) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10929
    | exact resolve eq10929 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10929
  have eq10984 : (M.op y (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10900 eq3186
    | exact resolve eq3186 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11898 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10449 eq10932
    | exact resolve eq10932 eq10449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10449 eq10932
  have eq11970 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq11898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11898
  have eq15385 : (σ (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10984 eq10900
    | exact resolve eq10900 eq10984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10900 eq10984
  have eq15409 : (σ (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15385
  have eq15475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15409 eq11970
    | exact resolve eq11970 eq15409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11970 eq15409
  have eq15505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15475
  have eq15539 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15505
       have r₂ := eq27
       grind)
    | exact resolve eq15505 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15505
  have eq15555 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15539 eq27
    | exact resolve eq27 eq15539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15556 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15539 eq70
    | (have r₁ := eq70
       have r₂ := eq15539
       grind)
    | exact resolve eq70 eq15539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq15557 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15539 eq83
    | (have r₁ := eq83
       have r₂ := eq15539
       grind)
    | exact resolve eq83 eq15539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq15562 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15539 eq397
    | exact resolve eq397 eq15539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq15568 : (M.op (σ y) (σ x)) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15539 eq3227
    | exact resolve eq3227 eq15539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227 eq15539
  have eq15569 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15557
  have eq15570 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15556
  have eq15689 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15570 eq88
    | exact resolve eq88 eq15570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq16591 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15569 eq15562
    | exact resolve eq15562 eq15569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15562
  have eq16593 : (σ y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15569 eq15568
    | exact resolve eq15568 eq15569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15568
  have eq16618 : (M.op (σ x) (σ y)) = (M.op y (M.op x y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15569 eq3186
    | exact resolve eq3186 eq15569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15569
  have eq16625 : (σ y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq16593
  have eq16627 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq16591
  have eq16631 : (M.op (σ x) (σ y)) = (M.op y (M.op x y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16618
    | exact resolve eq16618 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16618
  have eq16794 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq16627 eq15689
    | exact resolve eq15689 eq16627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15689 eq16627
  have eq16824 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq16794
  have eq16846 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq29 eq16824
    | exact resolve eq16824 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16824
  have eq16974 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16631 eq16625
    | exact resolve eq16625 eq16631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16625 eq16631
  have eq17008 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16974
  have eq19313 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq16846 eq122
    | exact resolve eq122 eq16846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq16846
  have eq19326 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by grind
  clear eq19313
  have eq19338 : y = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19326
       have r₂ := eq15555
       grind)
    | exact resolve eq19326 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15555 eq19326
  have eq21598 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq19338
       grind)
    | exact superpose eq19338 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq19338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19338
  have eq21599 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21598
  have eq21601 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21599
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21599
    | exact resolve eq21599 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21599
  have eq21602 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq21601
  have eq21612 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq21602
       grind)
    | exact superpose eq21602 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq21602
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21602
       grind)
    | exact resolve eq12 eq21602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21613 : y ≠ y ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq21602
       grind)
    | exact superpose eq21602 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21602
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21602
       grind)
    | exact resolve eq13 eq21602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21628 : (M.op y y) = (M.op x (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq638 y x
       have i₂ := eq21602
       grind)
    | exact superpose eq21602 eq638
    | exact resolve eq638 eq21602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq21632 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3186 x y
       have i₂ := eq21602
       grind)
    | exact superpose eq21602 eq3186
    | exact resolve eq3186 eq21602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21602
  have eq21633 : (k x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq21613
  have eq21634 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq21612
  have eq21635 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21632
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21632
    | exact resolve eq21632 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21632
  have eq21638 : (M.op y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3416 eq21628
    | exact resolve eq21628 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21628
  have eq21652 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21634
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21634
    | exact resolve eq21634 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21634
  have eq21653 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq21652
  have eq21697 : ∀ X0 : G, (M.op x y) = (M.op (k X0 (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21635 eq3711
    | exact resolve eq3711 eq21635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3711
  have eq21796 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq21653
       grind)
    | exact superpose eq21653 eq77
    | exact resolve eq77 eq21653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq21653
  have eq21812 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21796
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21796
    | exact resolve eq21796 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21796
  have eq22803 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21812 eq15570
    | exact resolve eq15570 eq21812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15570 eq21812
  have eq22806 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22803
  have eq22869 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22806 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq22806
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22806
       grind)
    | exact resolve eq13 eq22806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22806
  have eq22891 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22869
  have eq23029 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22891 eq93
    | exact resolve eq93 eq22891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq22891
  have eq23060 : (τ (σ y)) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23029
       have i₂ := eq9231
       grind)
    | exact superpose eq9231 eq23029
    | exact resolve eq23029 eq9231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9231 eq23029
  have eq23069 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq23060
    | exact resolve eq23060 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23060
  have eq23227 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21638 eq21635
    | exact resolve eq21635 eq21638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21635 eq21638
  have eq23268 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq23227
  have eq23346 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23069
       have i₂ := eq23268
       grind)
    | exact superpose eq23268 eq23069
    | exact resolve eq23069 eq23268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23069 eq23268
  have eq23369 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23346
  have eq23402 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23369 eq20
    | exact resolve eq20 eq23369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23536 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq23606 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23402
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23402
    | exact resolve eq23402 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23402
  have eq23723 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23606 eq17008
    | exact resolve eq17008 eq23606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17008 eq23606
  have eq23740 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq23723
  have eq23775 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23740
       have r₂ := eq27
       grind)
    | exact resolve eq23740 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23740
  have eq24000 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23775 eq65
    | exact resolve eq65 eq23775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq23775
  have eq24016 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq24000
    | exact resolve eq24000 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24000
  have eq24044 : x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq23369 eq24016
    | exact resolve eq24016 eq23369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23369
  have eq24071 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24044
       have r₂ := eq23536
       grind)
    | exact resolve eq24044 eq23536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23536 eq24044
  have eq24083 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21633
       have i₂ := eq24071
       grind)
    | exact superpose eq24071 eq21633
    | exact resolve eq21633 eq24071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21633 eq24071
  have eq24086 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq24083
  have eq32347 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24016 eq21697
    | exact resolve eq21697 eq24016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21697 eq24016
  have eq32516 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq32347
  have eq32587 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24086
       have i₂ := eq32516
       grind)
    | exact superpose eq32516 eq24086
    | exact resolve eq24086 eq32516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24086 eq32516
  have eq32610 : x = (M.op x y) := by grind
  clear eq32587
  have eq32641 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq32610 eq20
    | exact resolve eq20 eq32610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq32647 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq32610 eq82
    | (have r₁ := eq82
       have r₂ := eq32610
       grind)
    | exact resolve eq82 eq32610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq32688 : (M.op y x) = (M.op x x) := by
    first
    | exact superpose eq32610 eq218
    | exact resolve eq218 eq32610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq32713 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | exact superpose eq32610 eq3416
    | exact resolve eq3416 eq32610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416
  have eq32715 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op y x)) := by
    intro X0
    first
    | exact superpose eq32610 eq3489
    | exact resolve eq3489 eq32610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3489
  have eq32733 : y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq32647
  have eq32796 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq32641
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32641
    | exact resolve eq32641 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32641
  have eq32810 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq32796 eq26
    | exact resolve eq26 eq32796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33340 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq32713 X0
       have i₂ := eq32688
       grind)
    | exact superpose eq32688 eq32713
    | exact resolve eq32713 eq32688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32713
  have eq33342 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq32715 X0
       have i₂ := eq32688
       grind)
    | exact superpose eq32688 eq32715
    | exact resolve eq32715 eq32688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32715
  have eq42972 : y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq32733
       have i₂ := eq32688
       grind)
    | exact superpose eq32688 eq32733
    | exact resolve eq32733 eq32688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32733
  have eq42986 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq33340 X0
       have i₂ := eq42972
       grind)
    | exact superpose eq42972 eq33340
    | exact resolve eq33340 eq42972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33340
  have eq42990 : y = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq33342 x
       have i₂ := eq42972
       grind)
    | exact superpose eq42972 eq33342
    | exact resolve eq33342 eq42972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33342 eq42972
  have eq43297 : y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq42986 x
       grind)
    | exact superpose eq42986 eq18
    | (have j1 := eq42986 x
       grind)
    | exact resolve eq18 eq42986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq42986
  have eq43338 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq32610 eq43297
    | exact resolve eq43297 eq32610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43297
  have eq45445 : x ≠ y ∨ x = (k x y) := by grind
  clear eq42990
  have eq45448 : x = (k x y) := by
    first
    | (have r₁ := eq45445
       have r₂ := eq43338
       grind)
    | exact resolve eq45445 eq43338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43338 eq45445
  have eq45532 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq45448
       grind)
    | exact superpose eq45448 eq44
    | exact resolve eq44 eq45448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq45542 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2698 x y
       have i₂ := eq45448
       grind)
    | exact superpose eq45448 eq2698
    | (have j0 := eq2698 x y
       grind)
    | exact resolve eq2698 eq45448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698 eq45448
  have eq45549 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq45542
  have eq45557 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq45549
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45549
    | exact resolve eq45549 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45549
  have eq45565 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq32796 eq45532
    | exact resolve eq45532 eq32796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45532
  have eq45572 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq45557
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45557
    | exact resolve eq45557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45557
  have eq45579 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq45565
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45565
    | exact resolve eq45565 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45565
  have eq45585 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq45572
    | exact resolve eq45572 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq45572
  have eq45590 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq32796 eq45579
    | exact resolve eq45579 eq32796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45579
  have eq45596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq32796 eq45585
    | exact resolve eq45585 eq32796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45585
  have eq45602 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq45596
       have r₂ := eq27
       grind)
    | exact resolve eq45596 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45596
  have eq45608 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq45602
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45602
    | exact resolve eq45602 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45602
  have eq45613 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq32796 eq45608
    | exact resolve eq45608 eq32796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32796 eq45608
  have eq45618 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq45613
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45613
    | exact resolve eq45613 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq45613
  have eq45678 : (σ y) ≠ (σ y) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq45618 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ y)
       have r₂ := eq45618
       grind)
    | exact resolve eq13 eq45618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45698 : (M.op y (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq45618 eq3186
    | exact resolve eq3186 eq45618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45618
  have eq45701 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq45678
  have eq45705 : (M.op (σ x) (σ y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq32810 eq45698
    | exact resolve eq45698 eq32810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32810 eq45698
  have eq45725 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq45590 eq45701
    | exact resolve eq45701 eq45590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45590 eq45701
  have eq45729 : (M.op (σ x) (σ y)) = (M.op y x) := by
    first
    | exact superpose eq32610 eq45705
    | exact resolve eq45705 eq32610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45705
  have eq45746 : (M.op (σ x) (σ y)) = (M.op x x) := by
    first
    | (have i₁ := eq45729
       have i₂ := eq32688
       grind)
    | exact superpose eq32688 eq45729
    | exact resolve eq45729 eq32688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45729
  have eq45791 : (M.op y (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq45725 eq3186
    | exact resolve eq3186 eq45725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3186
  have eq45796 : (σ (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq45725 eq45791
    | exact resolve eq45791 eq45725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45725 eq45791
  have eq45817 : (σ (M.op x y)) = (M.op y x) := by
    first
    | exact superpose eq32610 eq45796
    | exact resolve eq45796 eq32610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32610 eq45796
  have eq45834 : (σ (M.op x y)) = (M.op x x) := by
    first
    | (have i₁ := eq45817
       have i₂ := eq32688
       grind)
    | exact superpose eq32688 eq45817
    | exact resolve eq45817 eq32688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32688 eq45817
  have eq53233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45834
       have i₂ := eq45746
       grind)
    | exact superpose eq45746 eq45834
    | exact resolve eq45834 eq45746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45746 eq45834
  have eq53234 : False := by grind
  exact eq53234

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq46
    | (have j0 := eq46 X0
       grind)
    | exact resolve eq46 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq75 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq27
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq85 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq95 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ x)
       have i₂ := eq76 x x
       grind)
    | exact superpose eq76 eq21
    | (have j1 := eq76 X0 X0
       grind)
    | exact resolve eq21 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq102 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq76 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq99 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq102 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq102 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq102 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq111
    | (have j0 := eq111 X0 X1
       grind)
    | exact resolve eq111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq191 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (M.op (σ X0) X1) (σ X2)) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq34
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq34 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq266 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107
    | exact resolve eq107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq277 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq266 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq266
    | (have j0 := eq266 X0
       grind)
    | exact resolve eq266 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq281 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq277
    | (have j0 := eq277 X0
       grind)
    | exact resolve eq277 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq331 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq363 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq331
    | (have j0 := eq331 X0 X1
       grind)
    | exact resolve eq331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq553 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq49 (σ X0)
       grind)
    | exact superpose eq49 eq27
    | (have j1 := eq49 (σ X0)
       grind)
    | exact resolve eq27 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq560 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq553 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq553
    | (have j0 := eq553 X0
       grind)
    | exact resolve eq553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq582 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq560 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq560
    | (have j0 := eq560 X0
       grind)
    | exact resolve eq560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq596 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq582 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq582
    | (have j0 := eq582 X0
       grind)
    | exact resolve eq582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq603 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq596 X0
       have j1 := eq29 X0
       grind)
    | (have r₁ := eq596 X0
       have r₂ := eq29 X0
       grind)
    | exact resolve eq596 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq596
  have eq608 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq603 (σ x)
       have i₂ := eq76 x x
       grind)
    | exact superpose eq76 eq603
    | (have j1 := eq76 X0 X0
       grind)
    | exact resolve eq603 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq613 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq27 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq603 (σ X0)
       grind)
    | exact superpose eq603 eq27
    | exact resolve eq27 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq603 (τ X0)
       grind)
    | exact superpose eq603 eq19
    | exact resolve eq19 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq622 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq617 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq617
    | (have j0 := eq617 X0
       grind)
    | exact resolve eq617 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq631 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq104
    | (have j0 := eq104 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq104 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq104
    | (have j0 := eq104 (τ X0) (τ X1)
       grind)
    | exact resolve eq104 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq639
    | (have j0 := eq639 X0 X1
       grind)
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq651 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq646 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq646
    | (have j0 := eq646 X0 X1
       grind)
    | exact resolve eq646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq654 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq651
    | (have j0 := eq651 X0 X1
       grind)
    | exact resolve eq651 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq656 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq654
    | (have j0 := eq654 X0 X1
       grind)
    | exact resolve eq654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq657 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq656 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq656
    | (have j0 := eq656 X0 X1
       grind)
    | exact resolve eq656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq658 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq896 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq85 x X2 X0 X1
       grind)
    | exact superpose eq85 eq9
    | exact resolve eq9 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq921 : ∀ X0 X2 : G, (M.op X2 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X2 X0) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq28 (M.op x X2) X2 X0
       have i₂ := eq896 X0 x X2
       grind)
    | exact superpose eq896 eq28
    | exact resolve eq28 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq922 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq896 x X1 X0
       grind)
    | exact superpose eq896 eq9
    | exact resolve eq9 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq95
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq95 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq962 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq961
  have eq1059 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq115 (τ X1) (τ X0)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq115
    | (have j0 := eq115 (τ (k X0 X1)) (τ X1)
       grind)
    | exact resolve eq115 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1059 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1059
    | (have j0 := eq1059 X0 X1
       grind)
    | exact resolve eq1059 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1081 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1077
    | (have j0 := eq1077 X0 X1
       grind)
    | exact resolve eq1077 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1084 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1081
    | (have j0 := eq1081 X0 X1
       grind)
    | exact resolve eq1081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1085 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1084 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1084
    | (have j0 := eq1084 X0 X1
       grind)
    | exact resolve eq1084 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1086 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1085 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1085
    | (have j0 := eq1085 X0 X1
       grind)
    | exact resolve eq1085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1087 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1086 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1086
    | (have j0 := eq1086 X0 X1
       grind)
    | exact resolve eq1086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1251 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1087 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq613 X0
       grind)
    | exact superpose eq613 eq1087
    | (have j0 := eq1087 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq1087 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1710 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq363 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq363
    | (have j0 := eq363 (τ X0) (τ X1)
       grind)
    | exact resolve eq363 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1783 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1710 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1710
    | (have j0 := eq1710 X0 X1
       grind)
    | exact resolve eq1710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq1930 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq921 (σ X0) (σ X0)
       have i₂ := eq622 X0
       grind)
    | exact superpose eq622 eq921
    | (have j1 := eq622 X0
       grind)
    | (have r₁ := eq921 (σ X0) (σ X0)
       have r₂ := eq622 X0
       grind)
    | exact resolve eq921 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq1932 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq1930 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq1938 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1932 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1932
    | (have j0 := eq1932 X0
       grind)
    | exact resolve eq1932 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq2631 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k (k X0 X0) X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1938 x
       have i₂ := eq363 x x
       grind)
    | exact superpose eq363 eq1938
    | (have j1 := eq363 X0 X0
       grind)
    | exact resolve eq1938 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq1938
  have eq2688 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k (k X0 X0) X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2631 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq9273 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq75 (k (σ x) (σ x)) x
       have i₂ := eq281 (σ x)
       grind)
    | exact superpose eq281 eq75
    | (have j0 := eq75 (σ X0) X0
       have j1 := eq281 (σ X0)
       grind)
    | exact resolve eq75 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq281
  have eq9337 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9273 X0
       have j1 := eq1087 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq9273 X0
       have r₂ := eq1087 (σ X0) (σ X0)
       grind)
    | exact resolve eq9273 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087 eq9273
  have eq9344 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9337 X0
       have j1 := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq9337 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq9337 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9337
  have eq9347 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9344 x
       have i₂ := eq27 (σ x) x
       grind)
    | exact superpose eq27 eq9344
    | (have j0 := eq9344 X0
       grind)
    | exact resolve eq9344 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9344
  have eq9348 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9347 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9347
    | (have j0 := eq9347 X0
       grind)
    | exact resolve eq9347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9347
  have eq9349 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9348 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq9348
    | (have j0 := eq9348 X0
       grind)
    | exact resolve eq9348 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9348
  have eq9368 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115 (k X0 X0) X0
       have i₂ := eq9349 X0
       grind)
    | exact superpose eq9349 eq115
    | (have j0 := eq115 X0 X0
       have j1 := eq9349 X0
       grind)
    | exact resolve eq115 eq9349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq9381 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq9349 (τ X0)
       grind)
    | exact superpose eq9349 eq19
    | (have j1 := eq9349 (τ X0)
       grind)
    | exact resolve eq19 eq9349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9349
  have eq9398 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq9368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9368
  have eq9417 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9381 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq9381
    | (have j0 := eq9381 X0
       grind)
    | exact resolve eq9381 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9381
  have eq9453 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9417 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9417
    | (have j0 := eq9417 X0
       grind)
    | exact resolve eq9417 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9417
  have eq9486 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9453 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq9453
    | (have j0 := eq9453 X0
       grind)
    | exact resolve eq9453 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9453
  have eq9518 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9486 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9486
    | (have j0 := eq9486 X0
       grind)
    | exact resolve eq9486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9486
  have eq9603 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq9518 (τ X0)
       grind)
    | exact superpose eq9518 eq19
    | (have j1 := eq9518 (τ X0)
       grind)
    | exact resolve eq19 eq9518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9518
  have eq9642 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9603 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq9603
    | (have j0 := eq9603 X0
       grind)
    | exact resolve eq9603 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9603
  have eq9678 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9642 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9642
    | (have j0 := eq9642 X0
       grind)
    | exact resolve eq9642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9642
  have eq9710 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9678 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq9678
    | (have j0 := eq9678 X0
       grind)
    | exact resolve eq9678 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9678
  have eq10326 : ∀ X0 : G, (σ (τ (k X0 X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq9710 X0
       grind)
    | exact superpose eq9710 eq614
    | (have j1 := eq9710 X0
       grind)
    | exact resolve eq614 eq9710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq9710
  have eq10380 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq10326 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq10326
    | (have j0 := eq10326 X0
       grind)
    | exact resolve eq10326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10326
  have eq10381 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq10380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10380
  have eq10553 : y ≠ y ∨ (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq962
       grind)
    | exact superpose eq962 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq962
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq962
       grind)
    | exact resolve eq12 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq10574 : (k x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq10553
  have eq11883 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq603 (σ X0)
       have i₂ := eq191 X0 (σ X0) X0
       grind)
    | exact superpose eq191 eq603
    | (have j1 := eq191 X0 (σ X0) x
       grind)
    | exact resolve eq603 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq603
  have eq11903 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq11883 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11883
  have eq11915 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11903 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11903
    | (have j0 := eq11903 X0
       grind)
    | exact resolve eq11903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11903
  have eq11969 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11915 X0
       have i₂ := eq10381 X0
       grind)
    | exact superpose eq10381 eq11915
    | (have j0 := eq11915 X0
       grind)
    | exact resolve eq11915 eq10381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11915
  have eq11991 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11969 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11969
    | exact resolve eq11969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12037 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq921 (σ X0) (σ X0)
       have i₂ := eq11969 X0
       grind)
    | exact superpose eq11969 eq921
    | (have j1 := eq11969 X0
       grind)
    | (have r₁ := eq921 (σ X0) (σ X0)
       have r₂ := eq11969 X0
       grind)
    | exact resolve eq921 eq11969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq11969
  have eq12053 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12037 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12037
  have eq12058 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12053 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq12053
    | (have j0 := eq12053 X0
       grind)
    | exact resolve eq12053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12053
  have eq12070 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11991 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq11991
    | (have j0 := eq11991 X0
       grind)
    | exact resolve eq11991 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq11991
  have eq12073 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12058 X0
       have j1 := eq9398 X0
       grind)
    | (have r₁ := eq12058 X0
       have r₂ := eq9398 X0
       grind)
    | exact resolve eq12058 eq9398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9398 eq12058
  have eq12080 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12070 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12070
    | (have j0 := eq12070 X0
       grind)
    | exact resolve eq12070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12070
  have eq12083 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12080 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq12080 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq12080 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12080
  have eq12165 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq12083 (τ X0)
       grind)
    | exact superpose eq12083 eq38
    | exact resolve eq38 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq12217 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12165 X0
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq12165
    | exact resolve eq12165 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12165
  have eq12799 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq922 (σ X0) (σ X0)
       have i₂ := eq12073 X0
       grind)
    | exact superpose eq12073 eq922
    | exact resolve eq922 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12828 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq12799 X0
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq12799
    | exact resolve eq12799 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12799
  have eq13215 : ∀ X0 : G, (σ (σ (k X0 X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12828 (σ X0)
       have i₂ := eq12073 X0
       grind)
    | exact superpose eq12073 eq12828
    | exact resolve eq12828 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13316 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13215 X0
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq13215
    | exact resolve eq13215 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq504415 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq922 (τ X1) (τ X0)
       have i₂ := eq1783 X0 X1
       grind)
    | exact superpose eq1783 eq922
    | (have j1 := eq1783 X0 X0
       grind)
    | exact resolve eq922 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq504530 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq504415 X0 X1
       have i₂ := eq12217 X0
       grind)
    | exact superpose eq12217 eq504415
    | (have j0 := eq504415 X0 X1
       grind)
    | exact resolve eq504415 eq12217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504415
  have eq504840 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq504530 X0 X1
       have i₂ := eq12217 X0
       grind)
    | exact superpose eq12217 eq504530
    | (have j0 := eq504530 X0 X1
       grind)
    | exact resolve eq504530 eq12217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12217 eq504530
  have eq505524 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0
       have i₂ := eq504840 (σ X0) X1
       grind)
    | exact superpose eq504840 eq613
    | (have j1 := eq504840 (σ X0) X1
       grind)
    | exact resolve eq613 eq504840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq504840
  have eq505874 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq505524 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq505524
    | (have j0 := eq505524 X0 X1
       grind)
    | exact resolve eq505524 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505524
  have eq505933 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq505874 X0 X1
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq505874
    | (have j0 := eq505874 X0 X1
       grind)
    | exact resolve eq505874 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505874
  have eq505978 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq505933 X0 X1
       have i₂ := eq12073 X0
       grind)
    | exact superpose eq12073 eq505933
    | (have j0 := eq505933 X0 X1
       grind)
    | exact resolve eq505933 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505933
  have eq506009 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq505978 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq505978
    | (have j0 := eq505978 X0 X1
       grind)
    | exact resolve eq505978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505978
  have eq506029 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq506009 X0 X1
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq506009
    | (have j0 := eq506009 X0 X1
       grind)
    | exact resolve eq506009 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506009
  have eq506046 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq506029 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq506029
    | (have j0 := eq506029 X0 X1
       grind)
    | exact resolve eq506029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506029
  have eq507420 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq506046 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq506046
    | (have j0 := eq506046 X1 X1
       grind)
    | exact resolve eq506046 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506046
  have eq508230 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq507420 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq507420
    | (have j0 := eq507420 X0 X1
       grind)
    | exact resolve eq507420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507420
  have eq508918 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq508230 X0 X1
       grind)
    | exact superpose eq508230 eq10
    | (have j1 := eq508230 X0 X1
       grind)
    | exact resolve eq10 eq508230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509504 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq508918 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq508918
    | (have j0 := eq508918 X1 X1
       grind)
    | exact resolve eq508918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508918
  have eq512671 : ∀ X0 X1 : G, (τ (σ X0)) ≠ X0 ∨ (M.op X0 X0) = (τ (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1258 X0
       have i₂ := eq509504 X0 (σ X0)
       grind)
    | exact superpose eq509504 eq1258
    | (have j1 := eq509504 X1 (σ X0)
       grind)
    | (have r₁ := eq1258 (M.op X1 X1)
       have r₂ := eq509504 (τ (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) X1
       grind)
    | exact resolve eq1258 eq509504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq509504
  have eq512776 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq512671 X0 X1
       grind)
    | (have r₁ := eq512671 X0 X1
       have r₂ := eq10 X0
       grind)
    | exact resolve eq512671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512671
  have eq512996 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq512776 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq512776
    | (have j0 := eq512776 X0 X1
       grind)
    | exact resolve eq512776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512776
  have eq513164 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq512996 X0 X1
       have i₂ := eq12073 X0
       grind)
    | exact superpose eq12073 eq512996
    | (have j0 := eq512996 X0 X1
       grind)
    | exact resolve eq512996 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512996
  have eq513287 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq513164 X0 X1
       have i₂ := eq12083 X0
       grind)
    | exact superpose eq12083 eq513164
    | (have j0 := eq513164 X0 X1
       grind)
    | exact resolve eq513164 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513164
  have eq527438 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq513287 X1 (σ X0)
       grind)
    | exact superpose eq513287 eq15
    | (have j1 := eq513287 X1 (σ X0)
       grind)
    | exact resolve eq15 eq513287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513287
  have eq560044 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq527438 x y
       grind)
    | exact superpose eq527438 eq16
    | (have j1 := eq527438 x y
       grind)
    | exact resolve eq16 eq527438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527438
  have eq563434 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq560044
       have i₂ := eq508230 x y
       grind)
    | exact superpose eq508230 eq560044
    | (have j1 := eq508230 y y
       grind)
    | (have r₁ := eq560044
       have r₂ := eq508230 x y
       grind)
    | exact resolve eq560044 eq508230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508230 eq560044
  have eq563437 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq563434
  have eq563438 : y = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq563437
  have eq563498 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12828 y
       have i₂ := eq563438
       grind)
    | exact superpose eq563438 eq12828
    | exact resolve eq12828 eq563438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563438
  have eq563644 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq563498
       have i₂ := eq12073 y
       grind)
    | exact superpose eq12073 eq563498
    | exact resolve eq563498 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563498
  have eq563661 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq563644
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq563644
    | exact resolve eq563644 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563644
  have eq566885 : (σ x) = (σ y) ∨ (σ x) = (σ (k (k y y) y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2688 y
       have i₂ := eq563661
       grind)
    | exact superpose eq563661 eq2688
    | (have j0 := eq2688 y
       grind)
    | exact resolve eq2688 eq563661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688
  have eq566992 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq631 y y
       have i₂ := eq563661
       grind)
    | exact superpose eq563661 eq631
    | (have j0 := eq631 y y
       grind)
    | (have r₁ := eq631 y y
       have r₂ := eq563661
       grind)
    | exact resolve eq631 eq563661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq563661
  have eq567061 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq566992
  have eq567069 : (σ y) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567061
       have i₂ := eq12073 y
       grind)
    | exact superpose eq12073 eq567061
    | exact resolve eq567061 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567061
  have eq567078 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq566885
       have i₂ := eq10381 y
       grind)
    | exact superpose eq10381 eq566885
    | exact resolve eq566885 eq10381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10381 eq566885
  have eq567091 : (σ y) = (σ (M.op y y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567069
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq567069
    | exact resolve eq567069 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567069
  have eq567092 : (σ y) = (σ (M.op y y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq567091
  have eq567095 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567078
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq567078
    | exact resolve eq567078 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567078
  have eq567096 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq567095
  have eq567108 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq567096
       have r₂ := eq567092
       grind)
    | exact resolve eq567096 eq567092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567092 eq567096
  have eq567109 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq567108
       grind)
    | exact superpose eq567108 eq16
    | exact resolve eq16 eq567108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567108
  have eq567125 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567109
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq567109
    | exact resolve eq567109 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567109
  have eq567128 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567125
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq567125
    | exact resolve eq567125 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567125
  have eq567129 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq567128
  have eq567930 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq13316 y
       have i₂ := eq567129
       grind)
    | exact superpose eq567129 eq13316
    | exact resolve eq13316 eq567129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13316 eq567129
  have eq568502 : (σ (σ y)) = (σ (k (σ y) (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq567930
       have i₂ := eq12073 (σ y)
       grind)
    | exact superpose eq12073 eq567930
    | exact resolve eq567930 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567930
  have eq568602 : (σ (σ y)) = (σ (σ (k y y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq568502
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq568502
    | exact resolve eq568502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568502
  have eq568654 : (σ x) = (σ (M.op y y)) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq568602
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq568602
    | exact resolve eq568602 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568602
  have eq575274 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq12828 y
       have i₂ := eq568654
       grind)
    | exact superpose eq568654 eq12828
    | exact resolve eq12828 eq568654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575298 : (M.op y y) = (τ (σ x)) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq568654
       grind)
    | exact superpose eq568654 eq10
    | exact resolve eq10 eq568654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568654
  have eq575839 : x = (M.op y y) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq575298
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq575298
    | exact resolve eq575298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575298
  have eq576312 : x = (M.op x y) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq922 y y
       have i₂ := eq575839
       grind)
    | exact superpose eq575839 eq922
    | exact resolve eq922 eq575839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq575839
  have eq581192 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq575274
       grind)
    | exact superpose eq575274 eq16
    | exact resolve eq16 eq575274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575274
  have eq583225 : (σ x) ≠ (σ x) ∨ (σ (σ y)) = (σ (σ (M.op y y))) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by
    first
    | (have i₁ := eq581192
       have i₂ := eq576312
       grind)
    | exact superpose eq576312 eq581192
    | exact resolve eq581192 eq576312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576312 eq581192
  have eq583227 : (σ x) ≠ (σ x) ∨ (σ (σ y)) = (σ (σ (M.op y y))) := by grind
  clear eq583225
  have eq583228 : (σ (σ y)) = (σ (σ (M.op y y))) := by grind
  clear eq583227
  have eq583280 : (σ (M.op y y)) = (τ (σ (σ y))) := by
    first
    | (have i₁ := eq10 (σ (M.op y y))
       have i₂ := eq583228
       grind)
    | exact superpose eq583228 eq10
    | exact resolve eq10 eq583228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583228
  have eq583880 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq583280
       have i₂ := eq10 (σ y)
       grind)
    | exact superpose eq10 eq583280
    | exact resolve eq583280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583280
  have eq585806 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq583880
       grind)
    | exact superpose eq583880 eq10
    | exact resolve eq10 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586387 : y = (M.op y y) := by
    first
    | (have i₁ := eq585806
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq585806
    | exact resolve eq585806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585806
  have eq587135 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104 x y
       have i₂ := eq10574
       grind)
    | exact superpose eq10574 eq104
    | (have j0 := eq104 x y
       grind)
    | exact resolve eq104 eq10574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq10574
  have eq587220 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq587135
  have eq587235 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq587220
       have r₂ := eq583880
       grind)
    | exact resolve eq587220 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587220
  have eq587243 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq587235
       have i₂ := eq12073 y
       grind)
    | exact superpose eq12073 eq587235
    | exact resolve eq587235 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587235
  have eq587250 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq587243
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq587243
    | exact resolve eq587243 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587243
  have eq587256 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq587250
       have i₂ := eq583880
       grind)
    | exact superpose eq583880 eq587250
    | exact resolve eq587250 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587250
  have eq587262 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq587256
       have i₂ := eq586387
       grind)
    | exact superpose eq586387 eq587256
    | exact resolve eq587256 eq586387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587256
  have eq642583 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq587262
       grind)
    | exact superpose eq587262 eq16
    | exact resolve eq16 eq587262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587262
  have eq642650 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq642583
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq642583
    | exact resolve eq642583 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642583
  have eq642652 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq642650
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq642650
    | exact resolve eq642650 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642650
  have eq642653 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq642652
  have eq642659 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq642653
       grind)
    | exact superpose eq642653 eq16
    | exact resolve eq16 eq642653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642689 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq642653
       grind)
    | exact superpose eq642653 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq642653
       grind)
    | exact resolve eq12 eq642653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642653
  have eq642755 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq642689
  have eq642771 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq642755
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq642755
    | exact resolve eq642755 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642755
  have eq642798 : (σ (k x y)) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq642771
       have i₂ := eq12073 y
       grind)
    | exact superpose eq12073 eq642771
    | exact resolve eq642771 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642771
  have eq642814 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq642798
       have i₂ := eq12083 y
       grind)
    | exact superpose eq12083 eq642798
    | exact resolve eq642798 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642798
  have eq642820 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq642814
       have i₂ := eq583880
       grind)
    | exact superpose eq583880 eq642814
    | exact resolve eq642814 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642814
  have eq644993 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq642820
       grind)
    | exact superpose eq642820 eq10
    | exact resolve eq10 eq642820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642820
  have eq645591 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq644993
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq644993
    | exact resolve eq644993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644993
  have eq647920 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq645591
       grind)
    | exact superpose eq645591 eq16
    | exact resolve eq16 eq645591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645591
  have eq647987 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq647920
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq647920
    | exact resolve eq647920 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647920
  have eq647989 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq647987
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq647987
    | exact resolve eq647987 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647987
  have eq647990 : (σ y) = (σ (k x y)) := by grind
  clear eq647989
  have eq648019 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq647990
       grind)
    | exact superpose eq647990 eq10
    | exact resolve eq10 eq647990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647990
  have eq648562 : y = (k x y) := by
    first
    | (have i₁ := eq648019
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq648019
    | exact resolve eq648019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648019
  have eq650547 : y ≠ y ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq658 x y
       have i₂ := eq648562
       grind)
    | exact superpose eq648562 eq658
    | (have j0 := eq658 x y
       grind)
    | (have r₁ := eq658 x y
       have r₂ := eq648562
       grind)
    | exact resolve eq658 eq648562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq648562
  have eq650612 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq650547
  have eq650666 : x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq650612
       have i₂ := eq586387
       grind)
    | exact superpose eq586387 eq650612
    | exact resolve eq650612 eq586387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586387 eq650612
  have eq650697 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq650666
       grind)
    | exact superpose eq650666 eq16
    | exact resolve eq16 eq650666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650666
  have eq650768 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq650697
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq650697
    | exact resolve eq650697 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650697
  have eq650770 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq650768
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq650768
    | exact resolve eq650768 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650768
  have eq650771 : y = (M.op x y) := by grind
  clear eq650770
  have eq652462 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq642659
       have i₂ := eq650771
       grind)
    | exact superpose eq650771 eq642659
    | exact resolve eq642659 eq650771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642659
  have eq652551 : (σ x) = (σ y) := by grind
  clear eq652462
  have eq652572 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq652551
       grind)
    | exact superpose eq652551 eq16
    | exact resolve eq16 eq652551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652874 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) := by
    first
    | (have i₁ := eq12828 y
       have i₂ := eq652551
       grind)
    | exact superpose eq652551 eq12828
    | exact resolve eq12828 eq652551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12828
  have eq652979 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq652874
       have i₂ := eq583880
       grind)
    | exact superpose eq583880 eq652874
    | exact resolve eq652874 eq583880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583880 eq652874
  have eq653181 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq652572
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq652572
    | exact resolve eq652572 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652572
  have eq653218 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq652979
       have i₂ := eq652551
       grind)
    | exact superpose eq652551 eq652979
    | exact resolve eq652979 eq652551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652979
  have eq653341 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq653181
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq653181
    | exact resolve eq653181 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653181
  have eq653355 : (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq653218
       have i₂ := eq12073 x
       grind)
    | exact superpose eq12073 eq653218
    | exact resolve eq653218 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12073 eq653218
  have eq653471 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq653341
       have i₂ := eq650771
       grind)
    | exact superpose eq650771 eq653341
    | exact resolve eq653341 eq650771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650771 eq653341
  have eq653479 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq653355
       have i₂ := eq12083 x
       grind)
    | exact superpose eq12083 eq653355
    | exact resolve eq653355 eq12083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12083 eq653355
  have eq653556 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq653471
       have i₂ := eq652551
       grind)
    | exact superpose eq652551 eq653471
    | exact resolve eq653471 eq652551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652551 eq653471
  have eq653619 : False := by grind
  exact eq653619

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq14 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y x) := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
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
  have eq70 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
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
  have eq75 : x ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq64 sF3
       grind)
    | exact superpose eq64 eq91
    | exact resolve eq91 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq95 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq64 y
       grind)
    | exact superpose eq64 eq93
    | exact resolve eq93 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq93
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq120 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq84 sF2 sF3
       grind)
    | exact superpose eq84 eq55
    | (have j1 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq121 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq125 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq123
    | exact resolve eq123 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq132 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq167 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq146 eq16
    | exact resolve eq16 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq194
    | exact resolve eq194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq198 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq195
       have r₂ := eq27
       grind)
    | exact resolve eq195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq200 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq198
    | exact resolve eq198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq200 eq27
    | exact resolve eq27 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X1 X0
       have i₂ := eq84 X0 (τ X1)
       grind)
    | exact superpose eq84 eq38
    | (have j1 := eq84 X0 (τ X1)
       grind)
    | exact resolve eq38 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq483 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq125
       grind)
    | exact superpose eq125 eq44
    | exact resolve eq44 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq125
  have eq486 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq483
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq483
    | exact resolve eq483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq599 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq50 X1 X0 X3
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq50 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y X0 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ y) X0 (σ x)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq200 eq76
    | (have r₁ := eq76
       have r₂ := eq200
       grind)
    | exact resolve eq76 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq740 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq739
  have eq745 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (M.op (σ y) (σ x))))) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq740 eq14
    | exact resolve eq14 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq851 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X1 (M.op X0 (M.op (σ x) (σ x))))) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq745 X0 (M.op X1 (M.op sF2 sF2))
       have i₂ := eq50 sF2 X1 sF3
       grind)
    | exact superpose eq50 eq745
    | exact resolve eq745 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq1050 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq200 eq602
    | exact resolve eq602 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ x))) = (M.op (M.op X1 (M.op (σ x) (σ x))) (M.op X0 (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1050 eq50
    | exact resolve eq50 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1067 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1057 eq14
    | exact resolve eq14 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1078 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1067 eq851
    | exact resolve eq851 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq1067
  have eq1088 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1078
  have eq1149 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1088 eq132
    | exact resolve eq132 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1165 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1149
    | exact resolve eq1149 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1255 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1165 eq127
    | exact resolve eq127 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1259 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq1255
  have eq1266 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1259
       have r₂ := eq202
       grind)
    | exact resolve eq1259 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq1259
  have eq1273 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq1266
       grind)
    | exact superpose eq1266 eq95
    | exact resolve eq95 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq1288 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1273
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1273
    | exact resolve eq1273 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1349 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1288 eq602
    | exact resolve eq602 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq1909 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1288 eq1349
    | exact resolve eq1349 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1919 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq1909
  have eq2000 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1919 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq13 eq1919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq2003 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2000
       have r₂ := eq1288
       grind)
    | exact resolve eq2000 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq2000
  have eq2207 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq200 eq2003
    | exact resolve eq2003 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq2003
  have eq2208 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2207
  have eq2209 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2208
    | exact resolve eq2208 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208
  have eq2214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2209 eq127
    | exact resolve eq127 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq2209
  have eq2217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2214
  have eq2221 : x = (M.op x y) := by
    first
    | (have r₁ := eq2217
       have r₂ := eq27
       grind)
    | exact resolve eq2217 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2283 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2221 eq20
    | exact resolve eq20 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2285 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq2221 eq75
    | (have r₁ := eq75
       have r₂ := eq2221
       grind)
    | exact resolve eq75 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2297 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) x) := by
    intro X0
    first
    | exact superpose eq2221 eq601
    | exact resolve eq601 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq2298 : (M.op y x) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq2285
  have eq2311 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2283
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2283
    | exact resolve eq2283 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283
  have eq2314 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2311 eq26
    | exact resolve eq26 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2328 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2311 eq486
    | exact resolve eq486 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq2350 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq2328
       have r₂ := eq27
       grind)
    | exact resolve eq2328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328
  have eq2473 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq2350 eq167
    | exact resolve eq167 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq2350
  have eq2475 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2221 eq2473
    | exact resolve eq2473 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq3368 : (M.op y x) = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2298
       have i₂ := eq2475
       grind)
    | exact superpose eq2475 eq2298
    | exact resolve eq2298 eq2475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298 eq2475
  have eq3370 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq95
       have i₂ := eq3368
       grind)
    | exact superpose eq3368 eq95
    | exact resolve eq95 eq3368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3386 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 (M.op y x)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1
       have i₂ := eq3368
       grind)
    | exact superpose eq3368 eq14
    | exact resolve eq14 eq3368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3368
  have eq3955 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq386
    | exact resolve eq386 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq386
  have eq3999 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (M.op X0 x)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq2221 eq3955
    | (have j0 := eq3955 X0
       grind)
    | exact resolve eq3955 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955
  have eq4013 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (σ (M.op X0 x)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq41 eq3999
    | (have j0 := eq3999 X0
       grind)
    | exact resolve eq3999 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3999
  have eq4021 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq2221 eq4013
    | (have j0 := eq4013 X0
       grind)
    | exact resolve eq4013 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4013
  have eq4027 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq2221 eq4021
    | (have j0 := eq4021 X0
       grind)
    | exact resolve eq4021 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021
  have eq4047 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq4027 (τ X0)
       grind)
    | exact superpose eq4027 eq34
    | (have j1 := eq4027 (τ X0)
       grind)
    | exact resolve eq34 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq4052 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq4027 y
       grind)
    | exact superpose eq4027 eq90
    | (have j1 := eq4027 y
       grind)
    | exact resolve eq90 eq4027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4027
  have eq4103 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2311 eq4052
    | exact resolve eq4052 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4052
  have eq4108 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq4047 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4047
    | (have j0 := eq4047 X0
       grind)
    | exact resolve eq4047 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq4122 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op (τ X0) x) := by
    intro X0
    first
    | exact superpose eq2311 eq4108
    | (have j0 := eq4108 X0
       grind)
    | exact resolve eq4108 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq4133 : (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4103
       have i₂ := eq3370
       grind)
    | exact superpose eq3370 eq4103
    | exact resolve eq4103 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370 eq4103
  have eq6265 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) (M.op X1 (M.op y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X1 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq599
    | (have j0 := eq599 X1 y X0 x
       grind)
    | exact resolve eq599 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq6349 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op (M.op X0 (M.op x x)) (M.op X1 (M.op y y))) := by
    intro X0 X1
    first
    | exact superpose eq2221 eq6265
    | exact resolve eq6265 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6265
  have eq8230 : ∀ X0 X1 : G, y = (M.op y (M.op X1 (M.op X0 (M.op x x)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq3386 X1 (M.op X0 (M.op x x))
       have i₂ := eq50 x X0 y
       grind)
    | exact superpose eq50 eq3386
    | exact resolve eq3386 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3386
  have eq8916 : ∀ X0 : G, (τ (k X0 (σ (M.op x y)))) = (M.op (τ X0) x) ∨ (τ X0) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) x)
       have i₂ := eq4122 X0
       grind)
    | exact superpose eq4122 eq16
    | (have j1 := eq4122 X0
       grind)
    | exact resolve eq16 eq4122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4122
  have eq9994 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 (σ (M.op x y)))) ∨ (τ X0) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have j0 := eq8916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8916
  have eq11891 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) x) ∨ y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4133 eq9994
    | (have j0 := eq9994 (σ y)
       grind)
    | exact resolve eq9994 eq4133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133 eq9994
  have eq11899 : (τ (σ y)) ≠ (M.op y y) ∨ (τ (σ y)) = (M.op (τ (σ y)) x) ∨ y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq132 eq11891
    | exact resolve eq11891 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq11891
  have eq11901 : y ≠ (M.op y y) ∨ (τ (σ y)) = (M.op (τ (σ y)) x) ∨ y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29 eq11899
    | exact resolve eq11899 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11899
  have eq11903 : y = (M.op y x) ∨ y ≠ (M.op y y) ∨ y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29 eq11901
    | exact resolve eq11901 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11901
  have eq11904 : y ≠ (M.op y y) ∨ y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq11903
  have eq12494 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq14 y (M.op X0 (M.op x x)) x
       have i₂ := eq6349 X0 x
       grind)
    | exact superpose eq6349 eq14
    | exact resolve eq14 eq6349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6349
  have eq12541 : y = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq8230 x y
       have i₂ := eq12494 x
       grind)
    | exact superpose eq12494 eq8230
    | exact resolve eq8230 eq12494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8230 eq12494
  have eq12782 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2297 X0
       have i₂ := eq12541
       grind)
    | exact superpose eq12541 eq2297
    | exact resolve eq2297 eq12541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq12785 : y ≠ y ∨ y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11904
       have i₂ := eq12541
       grind)
    | exact superpose eq12541 eq11904
    | (have r₁ := eq11904
       have r₂ := eq12541
       grind)
    | exact resolve eq11904 eq12541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11904 eq12541
  have eq12821 : y ≠ y ∨ y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq12785
  have eq12822 : y = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq12821
  have eq13440 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12782 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12782
    | (have j0 := eq12782 x
       grind)
    | exact resolve eq12782 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq12782
  have eq13454 : x = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2221 eq13440
    | exact resolve eq13440 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13440
  have eq13455 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq61
       have i₂ := eq13454
       grind)
    | exact superpose eq13454 eq61
    | exact resolve eq61 eq13454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq13456 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq13454
       grind)
    | exact superpose eq13454 eq70
    | exact resolve eq70 eq13454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq13454
  have eq13500 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2311 eq13456
    | exact resolve eq13456 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13456
  have eq13501 : (k y x) = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq13455
       have r₂ := eq2221
       grind)
    | exact resolve eq13455 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221 eq13455
  have eq13504 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13500
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13500
    | exact resolve eq13500 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13500
  have eq13506 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2311 eq13504
    | exact resolve eq13504 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13504
  have eq13511 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq13506 eq14
    | exact resolve eq14 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13909 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq90
       have i₂ := eq13501
       grind)
    | exact superpose eq13501 eq90
    | exact resolve eq90 eq13501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq13501
  have eq13921 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2311 eq13909
    | exact resolve eq13909 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13909
  have eq14095 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13921
       have i₂ := eq12822
       grind)
    | exact superpose eq12822 eq13921
    | exact resolve eq13921 eq12822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12822 eq13921
  have eq14139 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq14095
  have eq14146 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14139
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14139
    | exact resolve eq14139 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14139
  have eq14161 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14146 eq84
    | (have j0 := eq84 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq84 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq14146
  have eq14162 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq14161
  have eq16313 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq13506 eq13511
    | exact resolve eq13511 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13506 eq13511
  have eq16367 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq16313 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16313
  have eq16381 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14162 eq16367
    | exact resolve eq16367 eq14162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14162 eq16367
  have eq16413 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq16381
  have eq16420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2314 eq16413
    | exact resolve eq16413 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314 eq16413
  have eq16422 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq16420
       have r₂ := eq27
       grind)
    | exact resolve eq16420 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16420
  have eq16440 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16422 eq15
    | exact resolve eq15 eq16422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16422
  have eq16523 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16440
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16440
    | exact resolve eq16440 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16440
  have eq16559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2311 eq16523
    | exact resolve eq16523 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311 eq16523
  have eq16574 : False := by grind
  exact eq16574

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq28 (τ X0)
       grind)
    | exact superpose eq28 eq17
    | exact resolve eq17 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq30
    | exact resolve eq30 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq32
    | exact resolve eq32 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq32
  have eq40 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq50 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq26
    | exact resolve eq26 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq26
    | exact resolve eq26 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq33
    | exact resolve eq33 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq33
    | exact resolve eq33 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0)
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq20
    | exact resolve eq20 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq33 X1
       grind)
    | exact superpose eq33 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq84 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq109 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X0) X1 X2
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq19
    | exact resolve eq19 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X0 X0))) (M.op X2 (M.op X3 (M.op X0 X0))))) = (M.op (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X0 X0))) (M.op X2 (M.op X3 (M.op X0 X0))))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X2 (M.op X3 (M.op X0 X0))) X1 X0
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (τ X0)
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq20
    | exact resolve eq20 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq146 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ X0) (M.op X1 (M.op X2 (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq9
    | exact resolve eq9 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq65 (σ X0)
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq65
    | exact resolve eq65 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq76
    | exact resolve eq76 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X0 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq76
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq76
  have eq222 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198 X0 X1 X2
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq198
    | (have j0 := eq198 X0 X1 X2
       grind)
    | exact resolve eq198 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq198
  have eq223 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197 X0 X1 X2
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq197
    | (have j0 := eq197 X0 X1 X2
       grind)
    | exact resolve eq197 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq197
  have eq226 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq233 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       have j1 := eq64 X1 X0
       grind)
    | (have r₁ := eq226 X1 X0
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq226 (σ X0) (M.op X0 X0)
       have r₂ := eq64 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq226 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq226
  have eq250 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq65 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq66
    | exact resolve eq66 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq277 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq145 (M.op X0 X0)
       grind)
    | exact superpose eq145 eq146
    | exact resolve eq146 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq486 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq233
    | exact resolve eq233 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq233 (σ X0) X1
       grind)
    | exact superpose eq233 eq15
    | (have j1 := eq233 (σ X0) X1
       grind)
    | exact resolve eq15 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq525 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq486 X1 (τ X0)
       grind)
    | exact superpose eq486 eq17
    | (have j1 := eq486 X1 (τ X0)
       grind)
    | exact resolve eq17 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq115 x X2 X0 X1
       grind)
    | exact superpose eq115 eq9
    | exact resolve eq9 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq887 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq848 x X1 X0
       grind)
    | exact superpose eq848 eq9
    | exact resolve eq9 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq525 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq525
    | exact resolve eq525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq1186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1122 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1122
    | (have j0 := eq1122 X0 X1
       grind)
    | exact resolve eq1122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq2528 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq497 x y
       grind)
    | exact superpose eq497 eq16
    | (have j1 := eq497 x y
       grind)
    | exact resolve eq16 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq2820 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k (σ X0) X1)
       have i₂ := eq222 X0 X1 X2
       grind)
    | exact superpose eq222 eq13
    | (have j0 := eq13 (σ X2) (k (σ X0) X1)
       have j1 := eq222 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq222 X0 X1 X2
       grind)
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2826 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2820 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820
  have eq2827 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2826 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq2828 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2827 X0 X1 X2
       have i₂ := eq40 X0 X1 X2
       grind)
    | exact superpose eq40 eq2827
    | (have j0 := eq2827 X0 X1 X2
       grind)
    | exact resolve eq2827 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2827
  have eq2932 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k (σ X2) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq223 X0 X1 X2
       grind)
    | exact superpose eq223 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq223 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq223 X0 X1 X2
       grind)
    | exact resolve eq13 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq2938 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k (σ X2) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2932 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932
  have eq2939 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2938 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq2940 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2939 X0 X1 X2
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq2939
    | (have j0 := eq2939 X0 X1 X2
       grind)
    | exact resolve eq2939 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2939
  have eq3035 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2528
       have i₂ := eq1186 x y
       grind)
    | exact superpose eq1186 eq2528
    | (have j1 := eq1186 (σ x) (σ y)
       grind)
    | (have r₁ := eq2528
       have r₂ := eq1186 x y
       grind)
    | exact resolve eq2528 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq3036 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3035
  have eq3115 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq887 y x
       have i₂ := eq3036
       grind)
    | exact superpose eq3036 eq887
    | exact resolve eq887 eq3036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036
  have eq3127 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq887 (σ y) (σ x)
       have i₂ := eq3115
       grind)
    | exact superpose eq3115 eq887
    | exact resolve eq887 eq3115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq3115
  have eq3129 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3127
       have i₂ := eq33 y
       grind)
    | exact superpose eq33 eq3127
    | exact resolve eq3127 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127
  have eq3254 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq65 y
       have i₂ := eq3129
       grind)
    | exact superpose eq3129 eq65
    | exact resolve eq65 eq3129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq3129
  have eq3286 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3254
       have i₂ := eq33 y
       grind)
    | exact superpose eq33 eq3254
    | exact resolve eq3254 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254
  have eq3287 : (σ y) = (σ (M.op y y)) := by grind
  clear eq3286
  have eq3387 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq109 y X1 x
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq109
    | exact resolve eq109 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq3392 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq10
    | exact resolve eq10 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3453 : y = (M.op y y) := by
    first
    | (have i₁ := eq3392
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3392
    | exact resolve eq3392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3483 : ∀ X0 : G, (τ y) = (M.op (τ y) (M.op X0 (τ (M.op y y)))) := by
    intro X0
    first
    | (have i₁ := eq277 y x
       have i₂ := eq3453
       grind)
    | exact superpose eq3453 eq277
    | exact resolve eq277 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq3497 : ∀ X0 : G, (τ y) = (M.op (τ y) (M.op X0 (τ y))) := by
    intro X0
    first
    | (have i₁ := eq3483 X0
       have i₂ := eq3453
       grind)
    | exact superpose eq3453 eq3483
    | exact resolve eq3483 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3483
  have eq3876 : ∀ X0 X1 : G, (M.op X0 (τ y)) = (M.op (M.op X0 (τ y)) (M.op X1 (M.op (τ y) (τ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq848 X0 (τ y) (M.op X0 (τ y))
       have i₂ := eq3497 X0
       grind)
    | exact superpose eq3497 eq848
    | exact resolve eq848 eq3497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497
  have eq3880 : ∀ X0 X1 : G, (M.op X0 (τ y)) = (M.op (M.op X0 (τ y)) (M.op X1 (τ (M.op y y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3876 X0 X1
       have i₂ := eq84 y
       grind)
    | exact superpose eq84 eq3876
    | exact resolve eq3876 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3876
  have eq3893 : ∀ X0 X1 : G, (M.op X0 (τ y)) = (M.op (M.op X0 (τ y)) (M.op X1 (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq3880 X0 X1
       have i₂ := eq3453
       grind)
    | exact superpose eq3453 eq3880
    | exact resolve eq3880 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880
  have eq7219 : ∀ X0 : G, (σ (σ y)) = (M.op (σ (σ y)) (M.op X0 (σ (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq250 (σ y) X0
       have i₂ := eq3387 (σ y) (σ y)
       grind)
    | exact superpose eq3387 eq250
    | exact resolve eq250 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq3387
  have eq7287 : ∀ X0 : G, (σ (σ y)) = (M.op (σ (σ y)) (M.op X0 (σ (σ (M.op y y))))) := by
    intro X0
    first
    | (have i₁ := eq7219 X0
       have i₂ := eq33 y
       grind)
    | exact superpose eq33 eq7219
    | exact resolve eq7219 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7219
  have eq7309 : ∀ X0 : G, (σ (σ y)) = (M.op (σ (σ y)) (M.op X0 (σ (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq7287 X0
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq7287
    | exact resolve eq7287 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7287
  have eq7564 : ∀ X0 X1 : G, (M.op X0 (σ (σ y))) = (M.op (M.op X0 (σ (σ y))) (M.op X1 (M.op (σ (σ y)) (σ (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq848 X0 (σ (σ y)) (M.op X0 (σ (σ y)))
       have i₂ := eq7309 X0
       grind)
    | exact superpose eq7309 eq848
    | exact resolve eq848 eq7309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq7309
  have eq7568 : ∀ X0 X1 : G, (M.op X0 (σ (σ y))) = (M.op (M.op X0 (σ (σ y))) (M.op X1 (σ (M.op (σ y) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7564 X0 X1
       have i₂ := eq33 (σ y)
       grind)
    | exact superpose eq33 eq7564
    | exact resolve eq7564 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7564
  have eq7585 : ∀ X0 X1 : G, (M.op X0 (σ (σ y))) = (M.op (M.op X0 (σ (σ y))) (M.op X1 (σ (σ (M.op y y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7568 X0 X1
       have i₂ := eq33 y
       grind)
    | exact superpose eq33 eq7568
    | exact resolve eq7568 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7568
  have eq7596 : ∀ X0 X1 : G, (M.op X0 (σ (σ y))) = (M.op (M.op X0 (σ (σ y))) (M.op X1 (σ (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7585 X0 X1
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq7585
    | exact resolve eq7585 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7585
  have eq8499 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (τ y))) = (M.op (M.op X1 (M.op X0 (τ y))) (M.op X2 (M.op X0 (τ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (M.op X1 (τ y)) X1 X2
       have i₂ := eq3893 X1 X1
       grind)
    | exact superpose eq3893 eq19
    | exact resolve eq19 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq8525 : ∀ X0 X1 : G, (M.op X0 (τ y)) ≠ (M.op (M.op X0 (τ y)) (M.op X0 (τ y))) ∨ (k (M.op X1 (τ y)) (M.op X0 (τ y))) = (M.op (M.op X1 (τ y)) (M.op X0 (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 (τ y)) (M.op X0 (τ y))
       have i₂ := eq3893 X0 X1
       grind)
    | exact superpose eq3893 eq12
    | (have j0 := eq12 (M.op X1 (τ y)) (M.op X0 (τ y))
       grind)
    | exact resolve eq12 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8541 : ∀ X0 X1 : G, (k (M.op X1 (τ y)) (M.op X0 (τ y))) = (M.op (M.op X1 (τ y)) (M.op X0 (τ y))) := by
    intro X0 X1
    first
    | (have j0 := eq8525 X0 X1
       grind)
    | (have r₁ := eq8525 X1 X1
       have r₂ := eq3893 X1 X1
       grind)
    | exact resolve eq8525 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8525
  have eq8565 : ∀ X0 X1 : G, (M.op X1 (τ y)) = (k (M.op X1 (τ y)) (M.op X0 (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq8541 X0 X1
       have i₂ := eq3893 X1 X0
       grind)
    | exact superpose eq3893 eq8541
    | exact resolve eq8541 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8541
  have eq8931 : ∀ X0 : G, (τ (M.op y y)) = (k (τ (M.op y y)) (M.op X0 (τ y))) := by
    intro X0
    first
    | (have i₁ := eq8565 X0 (τ (M.op y y))
       have i₂ := eq145 y
       grind)
    | exact superpose eq145 eq8565
    | exact resolve eq8565 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq8565
  have eq8965 : ∀ X0 : G, (τ y) = (k (τ y) (M.op X0 (τ y))) := by
    intro X0
    first
    | (have i₁ := eq8931 X0
       have i₂ := eq3453
       grind)
    | exact superpose eq3453 eq8931
    | exact resolve eq8931 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8931
  have eq9151 : ∀ X0 : G, (k y (σ (M.op X0 (τ y)))) = (σ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq17 y (M.op X0 (τ y))
       have i₂ := eq8965 X0
       grind)
    | exact superpose eq8965 eq17
    | exact resolve eq17 eq8965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8965
  have eq9193 : ∀ X0 : G, y = (k y (σ (M.op X0 (τ y)))) := by
    intro X0
    first
    | (have i₁ := eq9151 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq9151
    | exact resolve eq9151 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9151
  have eq9236 : ∀ X0 X1 X2 : G, y = (k y (σ (M.op X0 (M.op (M.op X1 (M.op X2 (M.op (τ y) (τ y)))) (M.op X1 (M.op X2 (M.op (τ y) (τ y)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9193 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op (τ y) (τ y)))) (M.op X1 (M.op X2 (M.op (τ y) (τ y))))))
       have i₂ := eq113 (τ y) X0 X1 X2
       grind)
    | exact superpose eq113 eq9193
    | exact resolve eq9193 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq9193
  have eq9285 : ∀ X0 X1 X2 : G, y = (k y (σ (M.op X0 (M.op (M.op X1 (M.op X2 (τ (M.op y y)))) (M.op X1 (M.op X2 (τ (M.op y y)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9236 X0 X1 X2
       have i₂ := eq84 y
       grind)
    | exact superpose eq84 eq9236
    | exact resolve eq9236 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq9236
  have eq9296 : ∀ X0 X1 X2 : G, y = (k y (σ (M.op X0 (M.op (M.op X1 (M.op X2 (τ y))) (M.op X1 (M.op X2 (τ y))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9285 X0 X1 X2
       have i₂ := eq3453
       grind)
    | exact superpose eq3453 eq9285
    | exact resolve eq9285 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9285
  have eq9302 : ∀ X0 X1 X2 : G, y = (k y (σ (M.op X0 (M.op X1 (M.op X2 (τ y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9296 X0 X1 X2
       have i₂ := eq8499 X2 X1 X1
       grind)
    | exact superpose eq8499 eq9296
    | exact resolve eq9296 eq8499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8499 eq9296
  have eq9358 : ∀ X0 X1 : G, y = (k y (σ (M.op X1 (M.op X0 (τ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9302 X1 (M.op X0 (τ y)) x
       have i₂ := eq3893 X0 x
       grind)
    | exact superpose eq3893 eq9302
    | exact resolve eq9302 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893 eq9302
  have eq9442 : ∀ X0 X1 X2 : G, (τ (k X0 y)) = (k (τ X0) (k (τ y) (M.op X1 (M.op X2 (τ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 y (M.op X1 (M.op X2 (τ y))) X0
       have i₂ := eq9358 X2 X1
       grind)
    | exact superpose eq9358 eq50
    | exact resolve eq50 eq9358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq21196 : ∀ X0 X1 : G, (M.op X0 (σ (σ y))) ≠ (M.op (M.op X0 (σ (σ y))) (M.op X0 (σ (σ y)))) ∨ (k (M.op X1 (σ (σ y))) (M.op X0 (σ (σ y)))) = (M.op (M.op X1 (σ (σ y))) (M.op X0 (σ (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 (σ (σ y))) (M.op X0 (σ (σ y)))
       have i₂ := eq7596 X0 X1
       grind)
    | exact superpose eq7596 eq12
    | (have j0 := eq12 (M.op X1 (σ (σ y))) (M.op X0 (σ (σ y)))
       grind)
    | exact resolve eq12 eq7596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21212 : ∀ X0 X1 : G, (k (M.op X1 (σ (σ y))) (M.op X0 (σ (σ y)))) = (M.op (M.op X1 (σ (σ y))) (M.op X0 (σ (σ y)))) := by
    intro X0 X1
    first
    | (have j0 := eq21196 X0 X1
       grind)
    | (have r₁ := eq21196 X1 X1
       have r₂ := eq7596 X1 X1
       grind)
    | exact resolve eq21196 eq7596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21196
  have eq21247 : ∀ X0 X1 : G, (M.op X1 (σ (σ y))) = (k (M.op X1 (σ (σ y))) (M.op X0 (σ (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq21212 X0 X1
       have i₂ := eq7596 X1 X0
       grind)
    | exact superpose eq7596 eq21212
    | exact resolve eq21212 eq7596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7596 eq21212
  have eq23451 : ∀ X0 : G, (σ (σ (M.op y y))) = (k (σ (σ (M.op y y))) (M.op X0 (σ (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq21247 X0 (σ (σ (M.op y y)))
       have i₂ := eq154 y
       grind)
    | exact superpose eq154 eq21247
    | exact resolve eq21247 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq21247
  have eq23513 : ∀ X0 : G, (σ (σ y)) = (k (σ (σ y)) (M.op X0 (σ (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq23451 X0
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq23451
    | exact resolve eq23451 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23451
  have eq23756 : ∀ X0 : G, (k (σ y) (τ (M.op X0 (σ (σ y))))) = (τ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq42 (σ y) (M.op X0 (σ (σ y)))
       have i₂ := eq23513 X0
       grind)
    | exact superpose eq23513 eq42
    | exact resolve eq42 eq23513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq23513
  have eq23800 : ∀ X0 : G, (σ y) = (k (σ y) (τ (M.op X0 (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq23756 X0
       have i₂ := eq10 (σ y)
       grind)
    | exact superpose eq10 eq23756
    | exact resolve eq23756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23756
  have eq23881 : ∀ X0 X1 : G, (τ (k X0 (σ y))) = (k (τ X0) (k y (τ (τ (M.op X1 (σ (σ y))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 y (τ (M.op X1 (σ (σ y)))) X0
       have i₂ := eq23800 X1
       grind)
    | exact superpose eq23800 eq51
    | exact resolve eq51 eq23800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq23947 : ∀ X0 X1 : G, (k (τ X0) y) = (k (τ X0) (k y (τ (τ (M.op X1 (σ (σ y))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq23881 X0 X1
       have i₂ := eq26 X0 y
       grind)
    | exact superpose eq26 eq23881
    | exact resolve eq23881 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq23881
  have eq53592 : ∀ X0 X1 : G, (σ (k (τ X0) y)) = (M.op (σ (τ X0)) (k (σ y) (τ (M.op X1 (σ (σ y)))))) ∨ (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (σ (τ X0))) ∨ (σ (k (τ X0) y)) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2828 y (τ (M.op X1 (σ (σ y)))) (τ X0)
       have i₂ := eq23947 X0 X1
       grind)
    | exact superpose eq23947 eq2828
    | (have j0 := eq2828 y (τ (M.op X1 (σ (σ y)))) (τ X0)
       grind)
    | exact resolve eq2828 eq23947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828 eq23947
  have eq53837 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ y)) = (σ (k (τ X0) y)) ∨ (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (σ (τ X0))) ∨ (σ (k (τ X0) y)) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq53592 X0 X1
       have i₂ := eq23800 X1
       grind)
    | exact superpose eq23800 eq53592
    | (have j0 := eq53592 X0 X1
       grind)
    | exact resolve eq53592 eq23800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53592
  have eq53922 : ∀ X0 X1 : G, (k X0 (σ y)) = (M.op (σ (τ X0)) (σ y)) ∨ (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (σ (τ X0))) ∨ (σ (k (τ X0) y)) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq53837 X0 X1
       have i₂ := eq17 X0 y
       grind)
    | exact superpose eq17 eq53837
    | (have j0 := eq53837 X0 X1
       grind)
    | exact resolve eq53837 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53837
  have eq54005 : ∀ X0 X1 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (σ (τ X0))) ∨ (σ (k (τ X0) y)) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq53922 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53922
    | (have j0 := eq53922 X0 X1
       grind)
    | exact resolve eq53922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53922
  have eq54080 : ∀ X0 X1 : G, (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (k (τ X0) y)) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq54005 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54005
    | (have j0 := eq54005 X0 X1
       grind)
    | exact resolve eq54005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54005
  have eq54141 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (k (τ X0) y)) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq54080 X0 X0
       have i₂ := eq23800 X0
       grind)
    | exact superpose eq23800 eq54080
    | (have j0 := eq54080 X0 X1
       grind)
    | exact resolve eq54080 eq23800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54080
  have eq54196 : ∀ X0 X1 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (k (τ X0) y)) = (M.op (k (σ y) (τ (M.op X1 (σ (σ y))))) (k (σ y) (τ (M.op X1 (σ (σ y)))))) := by
    intro X0 X1
    first
    | (have j0 := eq54141 X0 X1
       have j1 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq54141 (σ y) X1
       have r₂ := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq54141 X0 X1
       have r₂ := eq12 X0 (σ y)
       grind)
    | exact resolve eq54141 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54141
  have eq54244 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k (τ X0) y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54196 X0 X0
       have i₂ := eq23800 X0
       grind)
    | exact superpose eq23800 eq54196
    | (have j0 := eq54196 X0 x
       grind)
    | exact resolve eq54196 eq23800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23800 eq54196
  have eq54283 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k X0 (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54244 X0
       have i₂ := eq17 X0 y
       grind)
    | exact superpose eq17 eq54244
    | (have j0 := eq54244 X0
       grind)
    | exact resolve eq54244 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq54244
  have eq54301 : ∀ X0 : G, (σ (M.op y y)) = (k X0 (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54283 X0
       have i₂ := eq33 y
       grind)
    | exact superpose eq33 eq54283
    | (have j0 := eq54283 X0
       grind)
    | exact resolve eq54283 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq54283
  have eq54315 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54301 X0
       have i₂ := eq3287
       grind)
    | exact superpose eq3287 eq54301
    | (have j0 := eq54301 X0
       grind)
    | exact resolve eq54301 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287 eq54301
  have eq54442 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq54315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54315
  have eq54650 : ∀ X0 X1 X2 : G, (σ (τ (k X0 y))) = (M.op (σ (τ X0)) (k y (σ (M.op X1 (M.op X2 (τ y)))))) ∨ (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (σ (τ X0))) ∨ (σ (τ (k X0 y))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2940 y (M.op X1 (M.op X2 (τ y))) (τ X0)
       have i₂ := eq9442 X0 X1 X2
       grind)
    | exact superpose eq9442 eq2940
    | (have j0 := eq2940 y (M.op X1 (M.op X2 (τ y))) (τ X0)
       grind)
    | exact resolve eq2940 eq9442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2940 eq9442
  have eq54911 : ∀ X0 X1 X2 : G, (σ (τ (k X0 y))) = (M.op (σ (τ X0)) y) ∨ (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (σ (τ X0))) ∨ (σ (τ (k X0 y))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54650 X0 X1 X2
       have i₂ := eq9358 X2 X1
       grind)
    | exact superpose eq9358 eq54650
    | (have j0 := eq54650 X0 X1 X2
       grind)
    | exact resolve eq54650 eq9358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54650
  have eq54989 : ∀ X0 X1 X2 : G, (M.op X0 y) = (σ (τ (k X0 y))) ∨ (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (σ (τ X0))) ∨ (σ (τ (k X0 y))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54911 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54911
    | (have j0 := eq54911 X0 X1 X2
       grind)
    | exact resolve eq54911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54911
  have eq55067 : ∀ X0 X1 X2 : G, (k X0 y) = (M.op X0 y) ∨ (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (σ (τ X0))) ∨ (σ (τ (k X0 y))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54989 X0 X1 X2
       have i₂ := eq11 (k X0 y)
       grind)
    | exact superpose eq11 eq54989
    | (have j0 := eq54989 X0 X1 X2
       grind)
    | exact resolve eq54989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54989
  have eq55137 : ∀ X0 X1 X2 : G, (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) X0) ∨ (k X0 y) = (M.op X0 y) ∨ (σ (τ (k X0 y))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55067 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55067
    | (have j0 := eq55067 X0 X1 X2
       grind)
    | exact resolve eq55067 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55067
  have eq55193 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op y X0) ∨ (k X0 y) = (M.op X0 y) ∨ (σ (τ (k X0 y))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55137 X0 X1 X0
       have i₂ := eq9358 X0 X1
       grind)
    | exact superpose eq9358 eq55137
    | (have j0 := eq55137 X0 X1 X2
       grind)
    | exact resolve eq55137 eq9358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55137
  have eq55243 : ∀ X0 X1 X2 : G, (k X0 y) = (M.op X0 y) ∨ (σ (τ (k X0 y))) = (M.op (k y (σ (M.op X1 (M.op X2 (τ y))))) (k y (σ (M.op X1 (M.op X2 (τ y)))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq55193 X0 X1 X2
       have j1 := eq12 X0 y
       grind)
    | (have r₁ := eq55193 y X1 X2
       have r₂ := eq12 y y
       grind)
    | (have r₁ := eq55193 X0 X1 X2
       have r₂ := eq12 X0 y
       grind)
    | exact resolve eq55193 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55193
  have eq55286 : ∀ X0 : G, (M.op y y) = (σ (τ (k X0 y))) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq55243 X0 x X0
       have i₂ := eq9358 X0 x
       grind)
    | exact superpose eq9358 eq55243
    | (have j0 := eq55243 X0 x x
       grind)
    | exact resolve eq55243 eq9358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9358 eq55243
  have eq55320 : ∀ X0 : G, (M.op y y) = (k X0 y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq55286 X0
       have i₂ := eq11 (k X0 y)
       grind)
    | exact superpose eq11 eq55286
    | (have j0 := eq55286 X0
       grind)
    | exact resolve eq55286 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55286
  have eq55334 : ∀ X0 : G, y = (k X0 y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq55320 X0
       have i₂ := eq3453
       grind)
    | exact superpose eq3453 eq55320
    | (have j0 := eq55320 X0
       grind)
    | exact resolve eq55320 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3453 eq55320
  have eq55492 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq55334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55334
  have eq55515 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq55492 X0
       have j1 := eq486 y X0
       grind)
    | (have r₁ := eq55492 x
       have r₂ := eq486 y x
       grind)
    | exact resolve eq55492 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq55492
  have eq55651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2528
       have i₂ := eq55515 x
       grind)
    | exact superpose eq55515 eq2528
    | exact resolve eq2528 eq55515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528
  have eq55654 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq55651
  have eq56268 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55654
       grind)
    | exact superpose eq55654 eq16
    | exact resolve eq16 eq55654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56305 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq54442 (σ x)
       have i₂ := eq55654
       grind)
    | exact superpose eq55654 eq54442
    | (have j0 := eq54442 (σ x)
       grind)
    | (have r₁ := eq54442 (σ x)
       have r₂ := eq55654
       grind)
    | exact resolve eq54442 eq55654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54442 eq55654
  have eq56318 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq56305
  have eq56324 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq56318
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq56318
    | exact resolve eq56318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56318
  have eq56338 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq56324
       have i₂ := eq55515 x
       grind)
    | exact superpose eq55515 eq56324
    | exact resolve eq56324 eq55515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55515 eq56324
  have eq56347 : False := by grind
  exact eq56347

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq80 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq224 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq228 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq235 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq225 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq225 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq225 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq236 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq228 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq228 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq228 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq228 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq252 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq236
    | (have j0 := eq236 X0 X1
       grind)
    | exact resolve eq236 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq253 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq259 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X0 X1
       have j1 := eq251 X0 X1
       grind)
    | (have r₁ := eq253 X0 X1
       have r₂ := eq251 X0 X1
       grind)
    | exact resolve eq253 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq253
  have eq260 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq259
    | exact resolve eq259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq259 x y
       grind)
    | exact superpose eq259 eq16
    | exact resolve eq16 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq358 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq260 X0 (τ X1)
       grind)
    | exact superpose eq260 eq18
    | exact resolve eq18 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq260
  have eq377 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq358 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq358
    | exact resolve eq358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq386 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq377
    | exact resolve eq377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq407 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq272
       have i₂ := eq386 x y
       grind)
    | exact superpose eq386 eq272
    | exact resolve eq272 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq386
  have eq408 : False := by grind
  exact eq408

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq295 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq296 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq300 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq294 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq294 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq294 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq313 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq300 (σ X0)
       grind)
    | exact superpose eq300 eq15
    | exact resolve eq15 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq313 X0
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq313
    | exact resolve eq313 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq313
  have eq377 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq332 X0
       grind)
    | exact superpose eq332 eq63
    | exact resolve eq63 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq296 (σ X0) (σ X1)
       grind)
    | exact superpose eq296 eq15
    | (have j1 := eq296 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq296 (τ X0) X1
       grind)
    | exact superpose eq296 eq18
    | (have j1 := eq296 (τ X0) X1
       grind)
    | exact resolve eq18 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq296
  have eq438 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 X1
       have i₂ := eq332 X1
       grind)
    | exact superpose eq332 eq421
    | (have j0 := eq421 X0 X1
       grind)
    | exact resolve eq421 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq421
  have eq589 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq429 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq429
    | exact resolve eq429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq640 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq589
    | (have j0 := eq589 X0 X1
       grind)
    | exact resolve eq589 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq1086 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq438 x y
       grind)
    | exact superpose eq438 eq16
    | (have j1 := eq438 x y
       grind)
    | exact resolve eq16 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq1146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1086
       have i₂ := eq640 x y
       grind)
    | exact superpose eq640 eq1086
    | (have j1 := eq640 x y
       grind)
    | (have r₁ := eq1086
       have r₂ := eq640 x y
       grind)
    | exact resolve eq1086 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq1086
  have eq1147 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1146
  have eq1153 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1147
       grind)
    | exact superpose eq1147 eq63
    | exact resolve eq63 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1155 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq377 y
       have i₂ := eq1147
       grind)
    | exact superpose eq1147 eq377
    | exact resolve eq377 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1176 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1155
       grind)
    | exact superpose eq1155 eq16
    | exact resolve eq16 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1197 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1176
       have i₂ := eq1153
       grind)
    | exact superpose eq1153 eq1176
    | exact resolve eq1176 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153 eq1176
  have eq1199 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1197
  have eq1200 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1199
  have eq1204 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq377 y
       have i₂ := eq1200
       grind)
    | exact superpose eq1200 eq377
    | exact resolve eq377 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq1205 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1200
       grind)
    | exact superpose eq1200 eq10
    | exact resolve eq10 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1249 : x = (M.op y y) := by
    first
    | (have i₁ := eq1205
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1205
    | exact resolve eq1205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1254 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq1249
       grind)
    | exact superpose eq1249 eq63
    | exact resolve eq63 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1249
  have eq1281 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1204
       grind)
    | exact superpose eq1204 eq16
    | exact resolve eq16 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1291 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1281
       have i₂ := eq1254
       grind)
    | exact superpose eq1254 eq1281
    | exact resolve eq1281 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254 eq1281
  have eq1292 : False := by grind
  exact eq1292

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq99 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
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
  have eq102 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq111 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq62 X1 X0 X3
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq382 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq67
  have eq383 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq382 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq384 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq383 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq395 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq384 (σ X0)
       grind)
    | exact superpose eq384 eq15
    | exact resolve eq15 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq395 X0
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq395
    | exact resolve eq395 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq395
  have eq598 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq16
    | (have j1 := eq97 x y
       grind)
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1603 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1664 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1603 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1603
    | (have j0 := eq1603 X0 X1
       grind)
    | exact resolve eq1603 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq5887 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq12
    | (have j0 := eq12 (τ X0) X1
       have j1 := eq99 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq99 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq99 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq12 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5898 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5887 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5887
  have eq12487 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq598
       have i₂ := eq1664 y x
       grind)
    | exact superpose eq1664 eq598
    | (have j1 := eq1664 (σ x) (σ y)
       grind)
    | (have r₁ := eq598
       have r₂ := eq1664 y x
       grind)
    | (have r₁ := eq598
       have r₂ := eq1664 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq598
       have r₂ := eq1664 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq598 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq1664
  have eq12488 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq12487
  have eq12490 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12488
       grind)
    | exact superpose eq12488 eq16
    | exact resolve eq16 eq12488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12488
  have eq12491 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq12490
       have r₂ := eq414 x
       grind)
    | exact resolve eq12490 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12490
  have eq14993 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq111 x X2 X0 X1
       grind)
    | exact superpose eq111 eq9
    | exact resolve eq9 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq15253 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq14993 x X1 X0
       grind)
    | exact superpose eq14993 eq9
    | exact resolve eq9 eq14993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14993
  have eq15439 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15253 x y
       have i₂ := eq12491
       grind)
    | exact superpose eq12491 eq15253
    | exact resolve eq15253 eq12491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12491
  have eq15694 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15253 (σ x) (σ y)
       have i₂ := eq15439
       grind)
    | exact superpose eq15439 eq15253
    | exact resolve eq15253 eq15439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15253 eq15439
  have eq15700 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15694
       have i₂ := eq414 x
       grind)
    | exact superpose eq414 eq15694
    | exact resolve eq15694 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15694
  have eq15708 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15700
       grind)
    | exact superpose eq15700 eq10
    | exact resolve eq10 eq15700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15700
  have eq15790 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15708
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15708
    | exact resolve eq15708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15708
  have eq15806 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15790
       grind)
    | exact superpose eq15790 eq16
    | exact resolve eq16 eq15790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15790
  have eq15807 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq15806
       have r₂ := eq414 x
       grind)
    | exact resolve eq15806 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15806
  have eq15825 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq15807
       grind)
    | exact superpose eq15807 eq10
    | exact resolve eq10 eq15807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15807
  have eq15908 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15825
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15825
    | exact resolve eq15825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15825
  have eq15909 : x = (M.op x x) := by grind
  clear eq15908
  have eq98109 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq5898 X0 X1
       grind)
    | exact superpose eq5898 eq18
    | (have j1 := eq5898 X0 X1
       grind)
    | exact resolve eq18 eq5898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5898
  have eq98339 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq98109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98109
  have eq98426 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98339 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98339
    | exact resolve eq98339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98339
  have eq98807 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98426 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq98426
    | (have j0 := eq98426 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq98426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98426
  have eq99095 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq98807 X0 X1
       grind)
    | exact superpose eq98807 eq10
    | (have j1 := eq98807 (k X0 X1) (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq10 eq98807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99219 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99095 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq99095
    | (have j0 := eq99095 (k X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq99095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99095
  have eq99521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq99219 (σ X0) (σ X1)
       grind)
    | exact superpose eq99219 eq15
    | (have j1 := eq99219 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq99219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99219
  have eq103201 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99521 x y
       grind)
    | exact superpose eq99521 eq16
    | (have j1 := eq99521 x y
       grind)
    | exact resolve eq16 eq99521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99521
  have eq103433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq103201
       have i₂ := eq98807 x y
       grind)
    | exact superpose eq98807 eq103201
    | (have j1 := eq98807 (σ x) (σ y)
       grind)
    | (have r₁ := eq103201
       have r₂ := eq98807 x y
       grind)
    | (have r₁ := eq103201
       have r₂ := eq98807 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq103201
       have r₂ := eq98807 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq103201 eq98807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98807 eq103201
  have eq103438 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq103433
  have eq103447 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103438
       grind)
    | exact superpose eq103438 eq16
    | exact resolve eq16 eq103438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103438
  have eq103450 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq103447
       have r₂ := eq414 x
       grind)
    | exact resolve eq103447 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103447
  have eq103451 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103450
       grind)
    | exact superpose eq103450 eq16
    | exact resolve eq16 eq103450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103452 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq103450
       grind)
    | exact superpose eq103450 eq10
    | exact resolve eq10 eq103450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103450
  have eq103579 : x = y := by
    first
    | (have i₁ := eq103452
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq103452
    | exact resolve eq103452 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103452
  have eq103580 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq103451
       have i₂ := eq414 x
       grind)
    | exact superpose eq414 eq103451
    | exact resolve eq103451 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq103451
  have eq103588 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq103580
       have i₂ := eq15909
       grind)
    | exact superpose eq15909 eq103580
    | exact resolve eq103580 eq15909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103580
  have eq103595 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq103588
       have i₂ := eq103579
       grind)
    | exact superpose eq103579 eq103588
    | exact resolve eq103588 eq103579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103579 eq103588
  have eq103598 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq103595
       have i₂ := eq15909
       grind)
    | exact superpose eq15909 eq103595
    | exact resolve eq103595 eq15909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15909 eq103595
  have eq103599 : False := by grind
  exact eq103599
