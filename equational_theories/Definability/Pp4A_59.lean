import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq22
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
  have eq59 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq73 x y
       grind)
    | exact superpose eq73 eq44
    | (have j1 := eq73 x y
       grind)
    | exact resolve eq44 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq73 sF2 sF3
       grind)
    | exact superpose eq73 eq55
    | (have j1 := eq73 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq104 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq103
    | exact resolve eq103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq106 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq104
    | exact resolve eq104 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq115 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ (k x y) = (M.op y y) := by
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
  have eq116 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq108 eq73
    | (have j0 := eq73 (σ x) (σ y)
       grind)
    | exact resolve eq73 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq27
    | exact resolve eq27 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq303 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq73 (τ X0) X1
       grind)
    | exact superpose eq73 eq34
    | (have j1 := eq73 (τ X0) X1
       grind)
    | exact resolve eq34 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq73
  have eq409 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq44
    | exact resolve eq44 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq106
  have eq412 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq409
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq409
    | exact resolve eq409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq429 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
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
  have eq489 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq116
    | (have r₁ := eq116
       have r₂ := eq126
       grind)
    | exact resolve eq116 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq490 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq489
  have eq495 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq490 eq108
    | exact resolve eq108 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq498 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq495
  have eq508 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq498 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq498
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq498
       grind)
    | exact resolve eq13 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq509 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq508
  have eq513 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq509
    | exact resolve eq509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq588 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq513 eq108
    | exact resolve eq108 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq513
  have eq591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq588
  have eq595 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq591
       have r₂ := eq27
       grind)
    | exact resolve eq591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq597 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (M.op X1 (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq595 eq50
    | exact resolve eq50 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq595 eq14
    | exact resolve eq14 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq597
    | (have j0 := eq597 X0 (σ x)
       grind)
    | exact resolve eq597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq661 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq126 eq637
    | exact resolve eq637 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq637
  have eq665 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq669 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x y))) = (M.op (M.op X1 (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq665 eq597
    | exact resolve eq597 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq665
  have eq673 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x y))) = (M.op (M.op X1 (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq669 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq721 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq673 eq599
    | exact resolve eq599 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq734 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq721 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq739 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq734 eq599
    | exact resolve eq599 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq734
  have eq747 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq739
  have eq750 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq747 eq595
    | exact resolve eq595 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq747
  have eq761 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq750
  have eq763 : y = (M.op x y) := by
    first
    | (have r₁ := eq761
       have r₂ := eq128
       grind)
    | exact resolve eq761 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq761
  have eq811 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq763 eq20
    | exact resolve eq20 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq815 : y ≠ y ∨ x = (M.op y x) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq763 eq115
    | (have r₁ := eq115
       have r₂ := eq763
       grind)
    | exact resolve eq115 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq821 : x = (M.op y x) ∨ (k x y) = (M.op y y) := by grind
  clear eq815
  have eq830 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq811
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq811
    | exact resolve eq811 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq842 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq830 eq412
    | exact resolve eq412 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq857 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq842
       have r₂ := eq27
       grind)
    | exact resolve eq842 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq866 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) y) := by
    intro X0
    first
    | exact superpose eq763 eq429
    | exact resolve eq429 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq879 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq857 eq59
    | exact resolve eq59 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq857
  have eq881 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq763 eq879
    | exact resolve eq879 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq897 : ∀ X0 X1 : G, (M.op X1 (M.op y y)) = (M.op (M.op X1 (M.op y y)) (M.op X0 (M.op y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 y X1 (M.op X0 (M.op y y))
       have i₂ := eq866 X0
       grind)
    | exact superpose eq866 eq50
    | exact resolve eq50 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq866
  have eq994 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq821
       have i₂ := eq881
       grind)
    | exact superpose eq881 eq821
    | exact resolve eq821 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq1064 : y ≠ (τ (M.op (σ x) (σ y))) ∨ (k y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq994
       grind)
    | exact superpose eq994 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq994
       grind)
    | exact resolve eq13 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6766 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op (M.op x y) X0)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq303
    | exact resolve eq303 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq303
  have eq6815 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op y X0)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq763 eq6766
    | (have j0 := eq6766 X0
       grind)
    | exact resolve eq6766 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6766
  have eq6828 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (M.op y X0)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq37 eq6815
    | (have j0 := eq6815 X0
       grind)
    | exact resolve eq6815 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq6815
  have eq6838 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq763 eq6828
    | (have j0 := eq6828 X0
       grind)
    | exact resolve eq6828 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6828
  have eq6846 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq763 eq6838
    | (have j0 := eq6838 X0
       grind)
    | exact resolve eq6838 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6838
  have eq6924 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq6846 y
       grind)
    | exact superpose eq6846 eq71
    | (have j1 := eq6846 y
       grind)
    | exact resolve eq71 eq6846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6846
  have eq6999 : (σ (M.op y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq830 eq6924
    | exact resolve eq6924 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6924
  have eq7033 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq6999
       have i₂ := eq994
       grind)
    | exact superpose eq994 eq6999
    | exact resolve eq6999 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994 eq6999
  have eq7074 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq7033
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq7033
    | exact resolve eq7033 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7033
  have eq7266 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7074 eq172
    | exact resolve eq172 eq7074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq7074
  have eq7283 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq763 eq7266
    | exact resolve eq7266 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7266
  have eq11557 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq7283
       have r₂ := eq1064
       grind)
    | exact resolve eq7283 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq7283
  have eq11563 : (k (σ y) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11557
       grind)
    | exact superpose eq11557 eq71
    | exact resolve eq71 eq11557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11557
  have eq11587 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11563
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq11563
    | exact resolve eq11563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11563
  have eq11599 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq830 eq11587
    | exact resolve eq11587 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11587
  have eq14164 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq14 y (M.op X0 (M.op y y)) x
       have i₂ := eq897 x X0
       grind)
    | exact superpose eq897 eq14
    | exact resolve eq14 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq14218 : y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y x
       have i₂ := eq14164 x
       grind)
    | exact superpose eq14164 eq14
    | exact resolve eq14 eq14164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14164
  have eq14261 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq14218
       grind)
    | exact superpose eq14218 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq14218
       grind)
    | exact resolve eq13 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14218
  have eq14262 : y = (k y y) := by grind
  clear eq14261
  have eq14269 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq14262
       grind)
    | exact superpose eq14262 eq71
    | exact resolve eq71 eq14262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq14262
  have eq14325 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq830 eq14269
    | exact resolve eq14269 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14269
  have eq14343 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq14325
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14325
    | exact resolve eq14325 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14325
  have eq14352 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq830 eq14343
    | exact resolve eq14343 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14343
  have eq14594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14352 eq11599
    | exact resolve eq11599 eq14352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11599 eq14352
  have eq14632 : x = (M.op y x) := by
    first
    | (have r₁ := eq14594
       have r₂ := eq27
       grind)
    | exact resolve eq14594 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14594
  have eq14665 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq14632
       grind)
    | exact superpose eq14632 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14632
       grind)
    | exact resolve eq13 eq14632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14632
  have eq14666 : (M.op x y) = (k x y) := by grind
  clear eq14665
  have eq14668 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14666
       have i₂ := eq881
       grind)
    | exact superpose eq881 eq14666
    | exact resolve eq14666 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq14666
  have eq14676 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14668
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14668
    | exact resolve eq14668 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq14668
  have eq14679 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq763 eq14676
    | exact resolve eq14676 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq14676
  have eq14703 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14679 eq15
    | exact resolve eq15 eq14679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14679
  have eq14778 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14703
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14703
    | exact resolve eq14703 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14703
  have eq14808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq830 eq14778
    | exact resolve eq14778 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq14778
  have eq14828 : False := by grind
  exact eq14828

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq67 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq70 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq88 y x
       grind)
    | exact superpose eq88 eq67
    | (have j1 := eq88 y x
       grind)
    | exact resolve eq67 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq88 sF3 sF2
       grind)
    | exact superpose eq88 eq77
    | (have j1 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq77 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq110 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq107
    | exact resolve eq107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq112 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq110
    | exact resolve eq110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq117
    | exact resolve eq117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq118
       have r₂ := eq27
       grind)
    | exact resolve eq118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq123 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123 eq27
    | exact resolve eq27 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq22 eq37
  have eq144 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq405 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq67
    | exact resolve eq67 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq408 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq405
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq405
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq456 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123 eq71
    | (have r₁ := eq71
       have r₂ := eq123
       grind)
    | exact resolve eq71 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq123
  have eq457 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq456
  have eq462 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq457 eq114
    | exact resolve eq114 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq466 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq462
  have eq473 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq466
       have r₂ := eq125
       grind)
    | exact resolve eq466 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq466
  have eq477 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq473 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq473
       grind)
    | exact resolve eq13 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq479 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq479 eq114
    | exact resolve eq114 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq479
  have eq505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq502
  have eq510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq505
    | exact resolve eq505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq505
  have eq512 : y = (M.op x y) := by
    first
    | (have r₁ := eq510
       have r₂ := eq27
       grind)
    | exact resolve eq510 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq514 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq512 eq20
    | exact resolve eq20 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq517 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq512 eq70
    | (have r₁ := eq70
       have r₂ := eq512
       grind)
    | exact resolve eq70 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq523 : x = (M.op x x) ∨ y = (k y x) := by grind
  clear eq517
  have eq531 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq514
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq514
    | exact resolve eq514 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq615 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq531 eq408
    | exact resolve eq408 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq618 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq615
       have r₂ := eq27
       grind)
    | exact resolve eq615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq631 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq618 eq144
    | exact resolve eq144 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq618
  have eq634 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq512 eq631
    | exact resolve eq631 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq804 : x = (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq523
       have i₂ := eq634
       grind)
    | exact superpose eq634 eq523
    | exact resolve eq523 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq634
  have eq807 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq804
       grind)
    | exact superpose eq804 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq804
       grind)
    | exact resolve eq13 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq810 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq936 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq112
       have i₂ := eq810 y
       grind)
    | exact superpose eq810 eq112
    | exact resolve eq112 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq810
  have eq945 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq936
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq936
    | exact resolve eq936 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq936
  have eq951 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq512 eq945
    | exact resolve eq945 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq945
  have eq952 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq951
  have eq961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq531 eq952
    | exact resolve eq952 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq965 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq961
       have r₂ := eq27
       grind)
    | exact resolve eq961 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq973 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq965 eq15
    | exact resolve eq15 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq988 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq973
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq973
    | exact resolve eq973 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq973
  have eq994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq531 eq988
    | exact resolve eq988 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq988
  have eq998 : False := by grind
  exact eq998

/-- `Equation4487`: `x ◇ (y ◇ y) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pyx_Equation4487 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4487 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4487.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X1 X2) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq399 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq695 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X1 X1)
       have i₂ := eq16 (M.op X1 (M.op X1 X1)) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X0 X0)
       have i₂ := eq16 (M.op X3 (M.op X0 X0)) X0 X1
       grind)
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op x X1) X1) := by
    intro X1
    first
    | (have i₁ := eq16 x x X1
       have i₂ := eq695 x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op x x)
       have i₂ := eq695 (M.op X1 (M.op x x))
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq696 eq16
    | exact resolve eq16 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq722 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq721 x x
       have i₂ := eq711 x x
       grind)
    | exact superpose eq711 eq721
    | exact resolve eq721 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq736 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x X1) (M.op x X1))) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op x X1) X1
       have i₂ := eq705 X1
       grind)
    | (have i₁ := eq16 X0 (M.op x y) y
       have i₂ := eq705 X1
       grind)
    | exact superpose eq705 eq16
    | exact resolve eq16 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op x (M.op X0 X0)) X0 X1
       have i₂ := eq705 (M.op X0 X0)
       grind)
    | exact superpose eq705 eq16
    | exact resolve eq16 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq740 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq736 x X1
       have i₂ := eq711 x (M.op x X1)
       grind)
    | exact superpose eq711 eq736
    | exact resolve eq736 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq743 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq711 X0 (M.op x x)
       have i₂ := eq695 (M.op x x)
       grind)
    | exact superpose eq695 eq711
    | exact resolve eq711 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op x x) X0) ∨ (M.op (M.op x y) y) = X0 ∨ (M.op (M.op x x) (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op x x) X0
       have i₂ := eq695 X0
       grind)
    | exact superpose eq695 eq11
    | (have j0 := eq11 (M.op x x) X0
       grind)
    | exact resolve eq11 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq768 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq797 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq832 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1 x
       have i₂ := eq711 x X1
       grind)
    | exact superpose eq711 eq774
    | (have j0 := eq774 X0 X1 x
       grind)
    | exact resolve eq774 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq836 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op (M.op x y) y) = (k (M.op x x) X0) ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq763 X0
       have i₂ := eq695 (M.op x x)
       grind)
    | exact superpose eq695 eq763
    | (have j0 := eq763 X0
       grind)
    | exact resolve eq763 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq763
  have eq837 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op x x) X0) ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | (have j0 := eq836 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq941 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq740 eq13
    | (have j0 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) (M.op (M.op x y) y)
       have r₂ := eq740 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq740 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq28 x (M.op (M.op x y) y)
       have r₂ := eq740 x
       grind)
    | exact resolve eq28 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq944 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq952 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq947 eq399
    | exact resolve eq399 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq968 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq952 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq952
    | exact resolve eq952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1075 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op x y) y) = X0 ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq743 eq11
    | (have j0 := eq11 (M.op (M.op x y) y) X0
       grind)
    | exact resolve eq11 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq1084 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1075 X0
       have j1 := eq941 X0
       grind)
    | (have r₁ := eq1075 X0
       have r₂ := eq941 (k (M.op (M.op x y) y) X0)
       grind)
    | (have r₁ := eq1075 X0
       have r₂ := eq941 X0
       grind)
    | (have r₁ := eq1075 (M.op (M.op x y) y)
       have r₂ := eq941 (M.op (M.op x y) y)
       grind)
    | exact resolve eq1075 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq1075
  have eq1087 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq1084 X0
       have j1 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq1084 x
       have r₂ := eq13 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq1084 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))
       grind)
    | exact resolve eq1084 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1093 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (σ x)) := by
    first
    | exact superpose eq1087 eq40
    | exact resolve eq40 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1087 eq42
    | exact resolve eq42 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) x) := by
    first
    | exact superpose eq1087 eq142
    | exact resolve eq142 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq2021 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq767
       grind)
    | exact superpose eq767 eq40
    | exact resolve eq40 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2023 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2021
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2021
    | exact resolve eq2021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq2025 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2023
    | exact resolve eq2023 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023
  have eq3185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2025 eq768
    | exact resolve eq768 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3193 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3185
       have r₂ := eq27
       grind)
    | exact resolve eq3185 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185
  have eq3198 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3193 eq220
    | exact resolve eq220 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3216 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3193 eq738
    | exact resolve eq738 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193
  have eq3219 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq3216
    | exact resolve eq3216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216
  have eq3231 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq3198
    | exact resolve eq3198 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3198
  have eq3238 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3231
       have r₂ := eq176
       grind)
    | exact resolve eq3231 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq3231
  have eq3240 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq3238
       have r₂ := eq13 y x
       grind)
    | exact resolve eq3238 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3238
  have eq3245 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq3240
       grind)
    | exact superpose eq3240 eq40
    | exact resolve eq40 eq3240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3240
  have eq3246 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3245
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3245
    | exact resolve eq3245 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245
  have eq3248 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3246
       have r₂ := eq177
       grind)
    | exact resolve eq3246 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq3246
  have eq3252 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3248 eq2025
    | exact resolve eq2025 eq3248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq3253 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3248 eq768
    | exact resolve eq768 eq3248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq3256 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | exact superpose eq3248 eq142
    | exact resolve eq142 eq3248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq3248
  have eq3257 : y = (k y x) := by
    first
    | exact superpose eq32 eq3256
    | exact resolve eq3256 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3262 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq767
       have i₂ := eq3257
       grind)
    | exact superpose eq3257 eq767
    | exact resolve eq767 eq3257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq3257
  have eq3268 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3252
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq3252
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq3252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3279 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq3252
       grind)
    | exact superpose eq3252 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3280 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq3252
       grind)
    | exact superpose eq3252 eq16
    | exact resolve eq16 eq3252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3287 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq738 y y
       have i₂ := eq3252
       grind)
    | exact superpose eq3252 eq738
    | exact resolve eq738 eq3252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq3288 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3279
  have eq3289 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq3268
  have eq3290 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3287
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3287
    | exact resolve eq3287 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287
  have eq3296 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3280 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3280
    | (have j0 := eq3280 X0
       grind)
    | exact resolve eq3280 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq3302 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3288 eq3289
    | exact resolve eq3289 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288 eq3289
  have eq3308 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3296 eq3302
    | exact resolve eq3302 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3302
  have eq3309 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3308
  have eq3322 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3253 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq3253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3253
  have eq3331 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3322
  have eq3833 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq711 X0 y
       have i₂ := eq3262
       grind)
    | exact superpose eq3262 eq711
    | exact resolve eq711 eq3262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3262
  have eq3883 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq3290 eq947
    | exact resolve eq947 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3904 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3290 eq1095
    | exact resolve eq1095 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq3956 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq3904
    | exact resolve eq3904 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904
  have eq4086 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3309
       grind)
    | exact superpose eq3309 eq41
    | exact resolve eq41 eq3309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq4094 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4086
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4086
    | exact resolve eq4086 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4086
  have eq4096 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4094
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4094
    | exact resolve eq4094 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq5074 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3956 eq796
    | (have j0 := eq796 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq796 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq3956
       grind)
    | exact resolve eq796 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq5075 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq5074
  have eq5076 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq5075
  have eq5992 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5076 eq738
    | exact resolve eq738 eq5076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5995 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3290 eq5992
    | exact resolve eq5992 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5992
  have eq6064 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5995 eq5076
    | exact resolve eq5076 eq5995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5076 eq5995
  have eq6091 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq6064
  have eq6122 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6091 eq29
    | exact resolve eq29 eq6091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6091
  have eq6166 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq6122
    | exact resolve eq6122 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6122
  have eq7932 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4096 eq832
    | (have j0 := eq832 (σ y) (σ y)
       grind)
    | exact resolve eq832 eq4096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq7989 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq7932
  have eq8017 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq7989
    | exact resolve eq7989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7989
  have eq8049 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3290 eq8017
    | exact resolve eq8017 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290 eq8017
  have eq14669 : y = (k y (τ (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8049 eq220
    | exact resolve eq220 eq8049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq14683 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq8049 eq16
    | exact resolve eq16 eq8049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14684 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8049 eq28
    | (have j0 := eq28 (σ y) (σ y)
       grind)
    | (have r₁ := eq28 (σ y) (σ y)
       have r₂ := eq8049
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq8049
       grind)
    | exact resolve eq28 eq8049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq14690 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq8049 eq698
    | exact resolve eq698 eq8049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14695 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14684
  have eq14701 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14690 x x
       have i₂ := eq711 x x
       grind)
    | exact superpose eq711 eq14690
    | exact resolve eq14690 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14690
  have eq14704 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4096 eq14695
    | exact resolve eq14695 eq4096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4096 eq14695
  have eq14705 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq8049 eq14683
    | exact resolve eq14683 eq8049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14683
  have eq14715 : y = (k y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq14669
    | exact resolve eq14669 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14669
  have eq14721 : (σ y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8049 eq14701
    | exact resolve eq14701 eq8049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8049 eq14701
  have eq14724 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq14704 eq14705
    | exact resolve eq14705 eq14704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14705
  have eq14732 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3309 eq14715
    | exact resolve eq14715 eq3309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14715
  have eq14734 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14704 eq14721
    | exact resolve eq14721 eq14704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14721
  have eq14741 : (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14732 eq14734
    | exact resolve eq14734 eq14732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14732 eq14734
  have eq14748 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq3296 eq14741
    | exact resolve eq14741 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296 eq14741
  have eq14756 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14704 eq26
    | exact resolve eq26 eq14704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14704
  have eq14854 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14724 eq14756
    | exact resolve eq14756 eq14724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14724 eq14756
  have eq14864 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14748 eq14854
    | exact resolve eq14854 eq14748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14748 eq14854
  have eq14865 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq14864
  have eq14872 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14865 eq29
    | exact resolve eq29 eq14865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq14954 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq14872
    | exact resolve eq14872 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14872
  have eq14969 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14954 eq27
    | exact resolve eq27 eq14954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15025 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14969
       have r₂ := eq6166
       grind)
    | exact resolve eq14969 eq6166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6166 eq14969
  have eq15029 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15025
       grind)
    | exact superpose eq15025 eq18
    | exact resolve eq18 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15041 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq740 x
       have i₂ := eq15025
       grind)
    | exact superpose eq15025 eq740
    | exact resolve eq740 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15055 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) (M.op x y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq968 X0
       have i₂ := eq15025
       grind)
    | exact superpose eq15025 eq968
    | exact resolve eq968 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq15071 : (τ (M.op (M.op x y) (M.op x y))) = (k (τ (M.op (M.op x y) (M.op x y))) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1097
       have i₂ := eq15025
       grind)
    | exact superpose eq15025 eq1097
    | exact resolve eq1097 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq15104 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3309
       have i₂ := eq15025
       grind)
    | exact superpose eq15025 eq3309
    | exact resolve eq3309 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq15114 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15104
  have eq15122 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3883 eq15114
    | exact resolve eq15114 eq3883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3883 eq15114
  have eq15123 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq15122
  have eq21376 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3219 eq947
    | exact resolve eq947 eq3219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947 eq3219
  have eq21519 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq15025 eq21376
    | (have j0 := eq21376 X0
       grind)
    | exact resolve eq21376 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21376
  have eq22346 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq711 X0 X1
       have i₂ := eq21519 (M.op X1 X1)
       grind)
    | exact superpose eq21519 eq711
    | (have j1 := eq21519 X1
       grind)
    | exact resolve eq711 eq21519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22349 : ∀ X0 X1 : G, (M.op X0 x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq21519 (M.op X1 x)
       grind)
    | exact superpose eq21519 eq16
    | (have j1 := eq21519 X1
       grind)
    | exact resolve eq16 eq21519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22406 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq15029 eq22349
    | (have j0 := eq22349 X0 X1
       grind)
    | exact resolve eq22349 eq15029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22349
  have eq22407 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq15025 eq22346
    | (have j0 := eq22346 X0 X1
       grind)
    | exact resolve eq22346 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22346
  have eq22435 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq21519 eq22407
    | (have j0 := eq22407 X0 X1
       have j1 := eq21519 X1
       grind)
    | exact resolve eq22407 eq21519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21519 eq22407
  have eq22450 : ∀ X1 : G, x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X1
    first
    | exact superpose eq22406 eq22435
    | (have j0 := eq22435 x X1
       have j1 := eq22406 x X1
       grind)
    | exact resolve eq22435 eq22406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22406 eq22435
  have eq22451 : ∀ X1 : G, (k X1 (M.op (σ x) (σ y))) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq22450 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22450
  have eq22469 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22451 eq798
    | (have j0 := eq798 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq798 (M.op (σ x) (σ y))
       have r₂ := eq22451 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq798 eq22451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22473 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22451 eq35
    | exact resolve eq35 eq22451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq22451
  have eq22484 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22469
  have eq22501 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22473 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq22473
    | exact resolve eq22473 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22473
  have eq22544 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22484 eq738
    | exact resolve eq738 eq22484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq22553 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15025 eq22544
    | exact resolve eq22544 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22544
  have eq22569 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22484 eq22553
    | exact resolve eq22553 eq22484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22484 eq22553
  have eq22839 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22569 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq22569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22852 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22839
  have eq23381 : (σ (M.op (σ x) (σ y))) ≠ (σ (M.op (σ x) (σ y))) ∨ (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22501 eq798
    | (have j0 := eq798 (σ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq798 (σ (M.op (σ x) (σ y)))
       have r₂ := eq22501 (σ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq798 eq22501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq22501
  have eq23411 : (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23381
  have eq24761 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23411 eq711
    | exact resolve eq711 eq23411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq24799 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15025 eq24761
    | exact resolve eq24761 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24761
  have eq24811 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22569 eq24799
    | exact resolve eq24799 eq22569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22569 eq24799
  have eq24906 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24811 eq23411
    | exact resolve eq23411 eq24811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23411 eq24811
  have eq24918 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24906
  have eq26142 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22852 eq42
    | exact resolve eq42 eq22852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq22852
  have eq26163 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq26142
    | exact resolve eq26142 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26142
  have eq26166 : (k (σ y) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14865 eq26163
    | exact resolve eq26163 eq14865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14865 eq26163
  have eq26169 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24918 eq26166
    | exact resolve eq26166 eq24918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26166
  have eq26180 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26169 eq3331
    | exact resolve eq3331 eq26169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3331 eq26169
  have eq26203 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26180
  have eq27189 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26203 eq27
    | exact resolve eq27 eq26203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26203
  have eq27312 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27189
       have r₂ := eq15123
       grind)
    | exact resolve eq27189 eq15123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15123 eq27189
  have eq27338 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27312 eq722
    | exact resolve eq722 eq27312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27343 : (M.op x y) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq27354 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq27338
    | exact resolve eq27338 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27338
  have eq27358 : (σ x) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27312 eq27354
    | exact resolve eq27354 eq27312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27312 eq27354
  have eq27361 : (σ x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14954 eq27358
    | exact resolve eq27358 eq14954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14954 eq27358
  have eq27379 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27361 eq15041
    | exact resolve eq15041 eq27361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15041
  have eq27391 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27361 eq15071
    | exact resolve eq15071 eq27361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27361
  have eq27451 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq27391
  have eq27463 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq27379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27379
  have eq27502 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq27451
    | exact resolve eq27451 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27451
  have eq28420 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq796 x x
       have i₂ := eq27502
       grind)
    | exact superpose eq27502 eq796
    | (have j0 := eq796 x x
       grind)
    | (have r₁ := eq796 x x
       have r₂ := eq27502
       grind)
    | exact resolve eq796 eq27502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27502
  have eq28421 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq28420
  have eq28422 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq28421
  have eq28590 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq28422
       grind)
    | exact superpose eq28422 eq16
    | exact resolve eq16 eq28422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28624 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28422 eq28590
    | exact resolve eq28590 eq28422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28422 eq28590
  have eq28994 : x = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27463 x
       have i₂ := eq28624 sF2
       grind)
    | exact superpose eq28624 eq27463
    | exact resolve eq27463 eq28624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28624
  have eq29001 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq28994
  have eq29172 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29001 eq32
    | exact resolve eq32 eq29001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29001
  have eq29324 : x = y ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq29172
    | exact resolve eq29172 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29172
  have eq29342 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15025 eq29324
    | exact resolve eq29324 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29324
  have eq29343 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq29342
  have eq29360 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29343 eq27
    | exact resolve eq27 eq29343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29365 : (M.op (M.op x y) y) = (M.op (M.op x y) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29343 eq722
    | exact resolve eq722 eq29343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq29448 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29343 eq24918
    | exact resolve eq24918 eq29343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29453 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq29448
  have eq29507 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq29453
    | exact resolve eq29453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29453
  have eq29563 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15025 eq29365
    | exact resolve eq29365 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29365
  have eq29565 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq29507
       have r₂ := eq29360
       grind)
    | exact resolve eq29507 eq29360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29360 eq29507
  have eq29625 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29565 eq26
    | exact resolve eq26 eq29565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29626 : x = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29565 eq30
    | exact resolve eq30 eq29565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29565
  have eq29716 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29343 eq29625
    | exact resolve eq29625 eq29343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29343 eq29625
  have eq29945 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29563 eq29716
    | exact resolve eq29716 eq29563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29563 eq29716
  have eq29963 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq29945
  have eq30017 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq29963 eq15055
    | exact resolve eq15055 eq29963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15055
  have eq30026 : (τ (M.op x y)) = (k (τ (M.op x y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29963 eq15071
    | exact resolve eq15071 eq29963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15071
  have eq30075 : (τ (M.op x y)) = (k (τ (M.op x y)) x) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq30026
  have eq30084 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq30017 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30017
  have eq30116 : x = (k x x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29626 eq30075
    | exact resolve eq30075 eq29626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30075
  have eq30124 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq29626 eq30084
    | exact resolve eq30084 eq29626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29626 eq30084
  have eq31514 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq796 x x
       have i₂ := eq30116
       grind)
    | exact superpose eq30116 eq796
    | (have j0 := eq796 x x
       grind)
    | (have r₁ := eq796 x x
       have r₂ := eq30116
       grind)
    | exact resolve eq796 eq30116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30116
  have eq31515 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq31514
  have eq31516 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq31515
  have eq31591 : (M.op x x) = (M.op (M.op x y) y) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq837 x
       have i₂ := eq30124 (M.op x x)
       grind)
    | exact superpose eq30124 eq837
    | (have j0 := eq837 (M.op x x)
       grind)
    | exact resolve eq837 eq30124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq30124
  have eq31621 : (M.op x x) = (M.op (M.op x y) y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq3833 eq31591
    | (have j1 := eq3833 x
       grind)
    | exact resolve eq31591 eq3833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833 eq31591
  have eq31631 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq15025 eq31621
    | exact resolve eq31621 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31621
  have eq31637 : (M.op x y) = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29963 eq31631
    | exact resolve eq31631 eq29963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31631
  have eq31639 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29963 eq31637
    | exact resolve eq31637 eq29963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29963 eq31637
  have eq31640 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq31639
  have eq32015 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq31516
       have i₂ := eq31640
       grind)
    | exact superpose eq31640 eq31516
    | exact resolve eq31516 eq31640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31516 eq31640
  have eq32058 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq32015
  have eq32131 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15029
       have i₂ := eq32058
       grind)
    | exact superpose eq32058 eq15029
    | exact resolve eq15029 eq32058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15029
  have eq32142 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq32058
  have eq32144 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq32131
       have r₂ := eq32142
       grind)
    | exact resolve eq32131 eq32142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32131
  have eq32260 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32144 eq27463
    | exact resolve eq27463 eq32144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27463 eq32144
  have eq32275 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq32260
  have eq32287 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32275
       have r₂ := eq27343
       grind)
    | exact resolve eq32275 eq27343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27343 eq32275
  have eq32299 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32287 eq32
    | exact resolve eq32 eq32287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq32287
  have eq32465 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq32299
    | exact resolve eq32299 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32299
  have eq32484 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15025 eq32465
    | exact resolve eq32465 eq15025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15025 eq32465
  have eq32485 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32484
  have eq32514 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32485 eq27
    | exact resolve eq27 eq32485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32602 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32485 eq24918
    | exact resolve eq24918 eq32485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24918 eq32485
  have eq32607 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq32602
  have eq32663 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq32607
       have r₂ := eq32142
       grind)
    | exact resolve eq32607 eq32142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32142 eq32607
  have eq32745 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq32663
    | exact resolve eq32663 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32663
  have eq32802 : x = (M.op x y) := by
    first
    | (have r₁ := eq32745
       have r₂ := eq32514
       grind)
    | exact resolve eq32745 eq32514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32514 eq32745
  have eq32847 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq32802
       grind)
    | exact superpose eq32802 eq18
    | exact resolve eq18 eq32802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq32848 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq32802
       grind)
    | exact superpose eq32802 eq22
    | exact resolve eq22 eq32802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq32802
  have eq32876 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32848 eq20
    | exact resolve eq20 eq32848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32848
  have eq33082 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq32847 eq740
    | exact resolve eq740 eq32847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq33106 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq32847 eq1093
    | exact resolve eq1093 eq32847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093 eq32847
  have eq33172 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq33106
    | exact resolve eq33106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq33106
  have eq33198 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq32876 eq33172
    | exact resolve eq33172 eq32876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33172
  have eq33404 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq33082 eq697
    | exact resolve eq697 eq33082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq34811 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq33198 eq796
    | (have j0 := eq796 (σ x) (σ x)
       grind)
    | (have r₁ := eq796 (σ x) (σ x)
       have r₂ := eq33198
       grind)
    | exact resolve eq796 eq33198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq33198
  have eq34812 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq34811
  have eq34813 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq34812
  have eq35044 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq34813 eq698
    | exact resolve eq698 eq34813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq35056 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq34813 eq35044
    | exact resolve eq35044 eq34813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34813 eq35044
  have eq35071 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq35056 x x
       have i₂ := eq33404 x x
       grind)
    | exact superpose eq33404 eq35056
    | exact resolve eq35056 eq33404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33404 eq35056
  have eq35088 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq35071 eq26
    | exact resolve eq26 eq35071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq35185 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33082 eq35088
    | exact resolve eq35088 eq33082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33082 eq35088
  have eq35228 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq35185 eq27
    | exact resolve eq27 eq35185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq35185
  have eq35328 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq32876 eq35228
    | exact resolve eq35228 eq32876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32876 eq35228
  have eq35331 : False := by grind
  exact eq35331

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_x_x_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq63 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | (have i₁ := eq14 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq211 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq64 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq65 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq65
    | exact resolve eq65 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq221 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq220 eq14
    | exact resolve eq14 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq221 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq221
    | exact resolve eq221 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq285 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq468 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq63 x x X2 X3 X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq63
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq469 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X5) := by
    intro X5
    first
    | (have i₁ := eq468 x x X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq468
    | exact resolve eq468 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq480 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq469 eq13
    | (have j0 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) x
       have r₂ := eq469 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq480 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq612 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X1 (σ X0)
       have i₂ := eq98 X0 X0
       grind)
    | exact superpose eq98 eq78
    | (have j0 := eq78 X1 (σ X0)
       have j1 := eq98 X0 X0
       grind)
    | (have r₁ := eq78 X0 (σ X1)
       have r₂ := eq98 X0 X1
       grind)
    | (have r₁ := eq78 X0 (σ X0)
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq78 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq98 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq621 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq620 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq625 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq612 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq634 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq625 X0 X1
       have j1 := eq78 X1 (σ X0)
       grind)
    | (have r₁ := eq625 X0 X1
       have r₂ := eq78 X0 (σ X0)
       grind)
    | exact resolve eq625 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq649 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq285 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq285
    | exact resolve eq285 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq1200 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq634 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq634
    | (have j0 := eq634 (τ X0) X1
       grind)
    | exact resolve eq634 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq1220 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1200 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1200
    | (have j0 := eq1200 X0 X1
       grind)
    | exact resolve eq1200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1231 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1220 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1220
    | (have j0 := eq1220 X0 X1
       grind)
    | exact resolve eq1220 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1251 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1231 (τ X0) X1
       have i₂ := eq649 X0 X0
       grind)
    | exact superpose eq649 eq1231
    | (have j0 := eq1231 (τ X0) X1
       grind)
    | exact resolve eq1231 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq1231
  have eq3847 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq486 eq621
    | (have j0 := eq621 (M.op (M.op x y) y)
       grind)
    | exact resolve eq621 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq3863 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq621 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq621
    | (have j0 := eq621 (τ X0)
       grind)
    | exact resolve eq621 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3879 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq3847
  have eq3883 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3863 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3863
    | (have j0 := eq3863 X0
       grind)
    | exact resolve eq3863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq3894 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3883 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3883
    | (have j0 := eq3883 X0
       grind)
    | exact resolve eq3883 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3883
  have eq16966 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq3879 eq211
    | exact resolve eq211 eq3879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16976 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3879 eq16966
    | exact resolve eq16966 eq3879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3879 eq16966
  have eq16998 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq16976 eq16
    | exact resolve eq16 eq16976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq17594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq17593
    | exact resolve eq17593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17593
  have eq17605 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq17594
       have r₂ := eq27
       grind)
    | exact resolve eq17594 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17594
  have eq17612 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17605 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq17605
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq17605
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq17605
       grind)
    | exact resolve eq13 eq17605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17605
  have eq17617 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq17612 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17612
  have eq17691 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq17617 eq88
    | exact resolve eq88 eq17617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq17617
  have eq17724 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq17691
    | exact resolve eq17691 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17691
  have eq17769 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq3894 (σ x)
       grind)
    | (have r₁ := eq17724
       have r₂ := eq3894 y
       grind)
    | exact resolve eq17724 eq3894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17724
  have eq348101 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) X0) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17769 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq17769
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq17769
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17769
       grind)
    | exact resolve eq13 eq17769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17769
  have eq348113 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq348101 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348101
  have eq351840 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq348113 eq1251
    | (have j0 := eq1251 (σ x) X0
       grind)
    | exact resolve eq1251 eq348113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq352124 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq348113 eq49
    | exact resolve eq49 eq348113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq348113
  have eq352183 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq351840 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351840
  have eq352205 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq28 eq352124
    | exact resolve eq352124 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352124
  have eq352260 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28 eq352183
    | exact resolve eq352183 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352183
  have eq352271 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3894 y
       grind)
    | (have r₁ := eq352205
       have r₂ := eq3894 x
       grind)
    | exact resolve eq352205 eq3894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894 eq352205
  have eq352308 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq352260 X0
       have j1 := eq78 X0 x
       grind)
    | (have r₁ := eq352260 X0
       have r₂ := eq78 X0 x
       grind)
    | (have r₁ := eq352260 X0
       have r₂ := eq78 X0 y
       grind)
    | exact resolve eq352260 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352260
  have eq352470 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq64 X0 y
       have i₂ := eq352271
       grind)
    | exact superpose eq352271 eq64
    | exact resolve eq64 eq352271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413239 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq352470 X0
       have i₂ := eq352470 sF0
       grind)
    | exact superpose eq352470 eq352470
    | exact resolve eq352470 eq352470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352470
  have eq413317 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq413239 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413239
  have eq544998 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq413317 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq413317
    | (have j0 := eq413317 x X0
       grind)
    | exact resolve eq413317 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545228 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq352271
       have i₂ := eq413317 y X0
       grind)
    | (have i₁ := eq352271
       have i₂ := eq413317 X0 y
       grind)
    | exact superpose eq413317 eq352271
    | exact resolve eq352271 eq413317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545231 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (k X1 x) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq352308 X1
       have i₂ := eq413317 y X0
       grind)
    | (have i₁ := eq352308 X1
       have i₂ := eq413317 X0 y
       grind)
    | exact superpose eq413317 eq352308
    | (have j0 := eq352308 X1
       grind)
    | exact resolve eq352308 eq413317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413317
  have eq545277 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq545228 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545228
  have eq545307 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq545231 X0 X1
       have j1 := eq78 X1 x
       grind)
    | (have r₁ := eq545231 y X1
       have r₂ := eq78 X0 y
       grind)
    | (have r₁ := eq545231 X0 X1
       have r₂ := eq78 X0 x
       grind)
    | exact resolve eq545231 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545231
  have eq545460 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq352271
       have i₂ := eq544998 y
       grind)
    | exact superpose eq544998 eq352271
    | exact resolve eq352271 eq544998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352271
  have eq545463 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq352308 X0
       have i₂ := eq544998 y
       grind)
    | exact superpose eq544998 eq352308
    | (have j0 := eq352308 X0
       grind)
    | exact resolve eq352308 eq544998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352308
  have eq545498 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16976
       have i₂ := eq544998 sF0
       grind)
    | exact superpose eq544998 eq16976
    | exact resolve eq16976 eq544998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544998
  have eq545509 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq545460
  have eq545529 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq545498
    | exact resolve eq545498 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545498
  have eq545544 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq545463 X0
       have j1 := eq78 X0 x
       grind)
    | (have r₁ := eq545463 X0
       have r₂ := eq78 X0 x
       grind)
    | exact resolve eq545463 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq545463
  have eq545582 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq64 X0 x
       have i₂ := eq545509
       grind)
    | exact superpose eq545509 eq64
    | exact resolve eq64 eq545509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549668 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq64 X0 x
       have i₂ := eq545529
       grind)
    | exact superpose eq545529 eq64
    | exact resolve eq64 eq545529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545529
  have eq549839 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq621 x
       have i₂ := eq545544 x
       grind)
    | exact superpose eq545544 eq621
    | (have j0 := eq621 x
       grind)
    | exact resolve eq621 eq545544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545544
  have eq550267 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq549839
  have eq550549 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq550267
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq550267
    | exact resolve eq550267 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550267
  have eq563250 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq550549 eq64
    | exact resolve eq64 eq550549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577507 : y = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16976
       have i₂ := eq545277 sF0
       grind)
    | exact superpose eq545277 eq16976
    | exact resolve eq16976 eq545277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545277
  have eq577532 : x = (M.op x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq577507
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq577507
    | exact resolve eq577507 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577507
  have eq631555 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq545582 eq545582
    | exact resolve eq545582 eq545582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545582
  have eq631665 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq631555 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631555
  have eq635567 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq549668 eq549668
    | exact resolve eq549668 eq549668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549668
  have eq635673 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have j0 := eq635567 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635567
  have eq694959 : (σ x) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq563250 eq550549
    | exact resolve eq550549 eq563250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550549 eq563250
  have eq694964 : (σ x) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq694959
  have eq695005 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq694964 eq222
    | exact resolve eq222 eq694964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq694964
  have eq695083 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq695005
    | exact resolve eq695005 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695005
  have eq695621 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq695083 eq220
    | exact resolve eq220 eq695083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq695083
  have eq695623 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq695621
    | exact resolve eq695621 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695621
  have eq796138 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq545509
       have i₂ := eq631665 x X0
       grind)
    | (have i₁ := eq545509
       have i₂ := eq631665 X0 x
       grind)
    | exact superpose eq631665 eq545509
    | exact resolve eq545509 eq631665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545509 eq631665
  have eq796152 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq796138 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796138
  have eq796228 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq469 eq796152
    | exact resolve eq796152 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq796152
  have eq799791 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq796228 eq14
    | exact resolve eq14 eq796228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796228
  have eq799800 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq799791 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq799791
    | (have j0 := eq799791 X0 X1
       grind)
    | exact resolve eq799791 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799791
  have eq799819 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq799800 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq799800
    | exact resolve eq799800 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq799800
  have eq814922 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq799819 eq16976
    | exact resolve eq16976 eq799819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814937 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq799819 eq695623
    | exact resolve eq695623 eq799819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695623 eq799819
  have eq814954 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq814937
  have eq814967 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq814922
    | exact resolve eq814922 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814922
  have eq814985 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq814954 eq27
    | exact resolve eq27 eq814954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814954
  have eq819374 : y = (M.op x y) := by
    first
    | (have r₁ := eq814985
       have r₂ := eq814967
       grind)
    | exact resolve eq814985 eq814967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814967 eq814985
  have eq819375 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq819374 eq20
    | exact resolve eq20 eq819374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq819577 : (M.op y y) = (σ (M.op y y)) := by
    first
    | exact superpose eq819374 eq16976
    | exact resolve eq16976 eq819374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16976
  have eq819578 : (M.op y y) = (τ (M.op y y)) := by
    first
    | exact superpose eq819374 eq16998
    | exact resolve eq16998 eq819374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16998
  have eq819880 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq819375
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq819375
    | exact resolve eq819375 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819375
  have eq819966 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq819880 eq26
    | exact resolve eq26 eq819880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq837570 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ y = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq819374 eq635673
    | (have j0 := eq635673 X0 X1
       grind)
    | exact resolve eq635673 eq819374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635673
  have eq839437 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (σ y) ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq577532
       have i₂ := eq837570 x X0
       grind)
    | (have i₁ := eq577532
       have i₂ := eq837570 X0 x
       grind)
    | exact superpose eq837570 eq577532
    | exact resolve eq577532 eq837570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577532 eq837570
  have eq839454 : ∀ X0 : G, y = (σ (M.op x y)) ∨ x = (M.op X0 x) ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq819880 eq839437
    | (have j0 := eq839437 X0
       grind)
    | exact resolve eq839437 eq819880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839437
  have eq839455 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq839454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839454
  have eq839701 : x = (M.op (M.op x y) y) ∨ y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq211 x x
       have i₂ := eq839455 (M.op x x)
       grind)
    | exact superpose eq839455 eq211
    | exact resolve eq211 eq839455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839455
  have eq839757 : x = (M.op y y) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq819374 eq839701
    | exact resolve eq839701 eq819374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839701
  have eq843347 : x = (σ x) ∨ y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq819577
       have i₂ := eq839757
       grind)
    | exact superpose eq839757 eq819577
    | exact resolve eq819577 eq839757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843371 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq211 y y
       have i₂ := eq839757
       grind)
    | exact superpose eq839757 eq211
    | exact resolve eq211 eq839757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839757
  have eq843379 : (M.op x y) = (M.op y y) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq819374 eq843371
    | exact resolve eq843371 eq819374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843371
  have eq843390 : y = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq843347
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq843347
    | exact resolve eq843347 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843347
  have eq843398 : (M.op x y) = (M.op y y) ∨ y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq843379
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq843379
    | exact resolve eq843379 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843379
  have eq843414 : y = (M.op y y) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq819374 eq843398
    | exact resolve eq843398 eq819374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843398
  have eq849193 : y = (σ y) ∨ y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq819577
       have i₂ := eq843414
       grind)
    | exact superpose eq843414 eq819577
    | exact resolve eq819577 eq843414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819577 eq843414
  have eq849219 : y = (σ y) ∨ y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq849193
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq849193
    | exact resolve eq849193 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq849193
  have eq849223 : y = (σ (M.op x y)) ∨ y = (σ (M.op x y)) := by
    first
    | exact superpose eq819880 eq849219
    | exact resolve eq849219 eq819880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819880 eq849219
  have eq849224 : y = (σ (M.op x y)) := by grind
  clear eq849223
  have eq849458 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq849224 eq819966
    | exact resolve eq819966 eq849224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819966
  have eq851201 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq849458
       have i₂ := eq545307 sF2 x
       grind)
    | exact superpose eq545307 eq849458
    | (have j1 := eq545307 X0 X0
       grind)
    | exact resolve eq849458 eq545307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545307
  have eq854049 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq621 x
       have i₂ := eq851201 x
       grind)
    | exact superpose eq851201 eq621
    | (have j0 := eq621 x
       grind)
    | exact resolve eq621 eq851201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq851201
  have eq854594 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq854049
  have eq854940 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq854594
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq854594
    | exact resolve eq854594 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq854594
  have eq863334 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq854940 eq211
    | exact resolve eq211 eq854940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq863343 : (M.op (σ x) (σ x)) = (M.op y y) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq819374 eq863334
    | exact resolve eq863334 eq819374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863334
  have eq1019731 : (σ x) = (M.op y y) ∨ y = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq863343 eq854940
    | exact resolve eq854940 eq863343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854940 eq863343
  have eq1019760 : (σ x) = (M.op y y) ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq1019731
  have eq1019874 : (σ x) = (τ (σ x)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq819578
       have i₂ := eq1019760
       grind)
    | exact superpose eq1019760 eq819578
    | exact resolve eq819578 eq1019760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819578 eq1019760
  have eq1019926 : y = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq1019874
    | exact resolve eq1019874 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1019874
  have eq1019965 : y ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq1019926 eq27
    | exact resolve eq27 eq1019926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019926
  have eq1020004 : x = (σ x) := by
    first
    | (have r₁ := eq1019965
       have r₂ := eq843390
       grind)
    | exact resolve eq1019965 eq843390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843390 eq1019965
  have eq1020517 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1020004 eq849458
    | exact resolve eq849458 eq1020004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849458 eq1020004
  have eq1020599 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1020517
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1020517
    | exact resolve eq1020517 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1020517
  have eq1020844 : y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq819374 eq1020599
    | exact resolve eq1020599 eq819374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819374 eq1020599
  have eq1021186 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1020844 eq27
    | exact resolve eq27 eq1020844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1020844
  have eq1021225 : False := by grind
  exact eq1021225

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq64 X0 (M.op x x)
       have i₂ := eq64 (M.op x x) x
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq64 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq65 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq65
    | exact resolve eq65 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq215 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq214 eq14
    | exact resolve eq14 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq216 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq215 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq215
    | exact resolve eq215 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq215
  have eq348 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq202 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) y)
       have r₂ := eq202 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq352 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq348 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq460 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq112 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq112
    | (have j0 := eq112 (σ X0)
       grind)
    | exact resolve eq112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq78 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq78 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq813 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq797 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq814 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq813 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq822 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq814
    | (have j0 := eq814 X0 X1
       grind)
    | exact resolve eq814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq3736 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq460 X0
       grind)
    | exact superpose eq460 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq460 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq460 X0
       grind)
    | exact resolve eq13 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3749 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq3756 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3736 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq3736 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq3736 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736
  have eq7122 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq822 X0 X1
       have j1 := eq810 X0 X1
       grind)
    | (have r₁ := eq822 X0 X1
       have r₂ := eq810 X0 X1
       grind)
    | (have r₁ := eq822 X1 X1
       have r₂ := eq810 X1 X1
       grind)
    | exact resolve eq822 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq822
  have eq7126 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7122 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7122
    | exact resolve eq7122 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7207 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7122 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7122
    | (have j0 := eq7122 x X0
       grind)
    | exact resolve eq7122 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7122
  have eq7340 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7126 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq7126
    | (have j0 := eq7126 X0 X1
       grind)
    | exact resolve eq7126 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq7126
  have eq12751 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3756 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq3756
    | (have j0 := eq3756 (τ X0) X1
       grind)
    | exact resolve eq3756 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3756
  have eq12769 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12751 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12751
    | (have j0 := eq12751 X0 X1
       grind)
    | exact resolve eq12751 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12751
  have eq12780 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12769 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12769
    | (have j0 := eq12769 X0 X1
       grind)
    | exact resolve eq12769 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12769
  have eq16335 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7207 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7207
    | (have j0 := eq7207 y
       grind)
    | exact resolve eq7207 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7207
  have eq16348 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16335
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16335
    | exact resolve eq16335 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16335
  have eq16365 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq16348
    | exact resolve eq16348 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16348
  have eq16872 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7340 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7340
    | (have j0 := eq7340 X1 X1
       grind)
    | exact resolve eq7340 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7340
  have eq17403 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq16872 y x
       grind)
    | exact superpose eq16872 eq75
    | (have j1 := eq16872 x x
       grind)
    | exact resolve eq75 eq16872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq16872
  have eq17645 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17403
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17403
    | exact resolve eq17403 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17403
  have eq17658 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq17645
    | exact resolve eq17645 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17645
  have eq17672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17658 eq16365
    | exact resolve eq16365 eq17658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16365 eq17658
  have eq17679 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17672
       have r₂ := eq27
       grind)
    | exact resolve eq17672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17672
  have eq17701 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq17679 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq17679
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq17679
       grind)
    | exact resolve eq13 eq17679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17679
  have eq17714 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq17701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17701
  have eq18261 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq17714 X1
       grind)
    | exact superpose eq17714 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq17714 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq17714 X0
       grind)
    | exact resolve eq13 eq17714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17714
  have eq18273 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq18261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18261
  have eq18312 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq18273 (k sF2 sF2) x
       grind)
    | exact superpose eq18273 eq49
    | (have j1 := eq18273 X0 x
       grind)
    | exact resolve eq49 eq18273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq18273
  have eq18401 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq18312
    | (have j0 := eq18312 x
       grind)
    | exact resolve eq18312 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18312
  have eq18437 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq18401 X0
       have j1 := eq12780 x X0
       grind)
    | (have r₁ := eq18401 X0
       have r₂ := eq12780 x x
       grind)
    | (have r₁ := eq18401 x
       have r₂ := eq12780 x x
       grind)
    | exact resolve eq18401 eq12780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12780 eq18401
  have eq18494 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq18437 x
       grind)
    | exact superpose eq18437 eq112
    | (have j0 := eq112 x
       grind)
    | exact resolve eq112 eq18437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq18437
  have eq18518 : x = (M.op x x) := by grind
  clear eq18494
  have eq18610 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq204 x x
       have i₂ := eq18518
       grind)
    | exact superpose eq18518 eq204
    | exact resolve eq204 eq18518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18618 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18610
       have i₂ := eq18518
       grind)
    | exact superpose eq18518 eq18610
    | exact resolve eq18610 eq18518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18518 eq18610
  have eq19255 : x = (M.op x (σ y)) := by
    first
    | exact superpose eq18618 eq216
    | exact resolve eq216 eq18618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq19273 : x = (M.op x y) := by
    first
    | exact superpose eq18618 eq204
    | exact resolve eq204 eq18618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19280 : x = (M.op x y) := by
    first
    | (have i₁ := eq19273
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19273
    | exact resolve eq19273 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19273
  have eq19293 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19280 eq20
    | exact resolve eq20 eq19280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19280
  have eq19455 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19293
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19293
    | exact resolve eq19293 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19293
  have eq20268 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19455 eq26
    | exact resolve eq26 eq19455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq20410 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq352 eq3749
    | (have j0 := eq3749 (M.op (M.op x y) y)
       grind)
    | exact resolve eq3749 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq3749
  have eq20452 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq20410
  have eq20474 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18618 eq20452
    | exact resolve eq20452 eq18618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20452
  have eq20495 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20474
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20474
    | exact resolve eq20474 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20474
  have eq20506 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19455 eq20495
    | exact resolve eq20495 eq19455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19455 eq20495
  have eq20519 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20506 eq204
    | exact resolve eq204 eq20506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq20527 : (σ (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq20506 eq20519
    | exact resolve eq20519 eq20506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20506 eq20519
  have eq20539 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq18618 eq20527
    | exact resolve eq20527 eq18618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18618 eq20527
  have eq24917 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq20539 eq20268
    | exact resolve eq20268 eq20539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268
  have eq24918 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19255 eq24917
    | exact resolve eq24917 eq19255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19255 eq24917
  have eq24922 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq24918 eq27
    | exact resolve eq27 eq24918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq24918
  have eq24923 : False := by grind
  exact eq24923

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have r₂ := eq9 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
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
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq58 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq58 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq58 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq59 (σ X0)
       grind)
    | exact superpose eq59 eq15
    | exact resolve eq15 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq61
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq61
  have eq84 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq90
  have eq136 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq139 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq164 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))
       have i₂ := eq139 (τ X0) X1 X2
       grind)
    | exact superpose eq139 eq17
    | exact resolve eq17 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq170 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq164 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164
    | exact resolve eq164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq363 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq372 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq376 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq372 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq372 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq372 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq386 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq376 X0 X1
       have j1 := eq84 X1 (σ X0)
       grind)
    | (have r₁ := eq376 X0 X0
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq376 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq376
  have eq394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq386 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq386
    | (have j0 := eq386 X0 X1
       grind)
    | exact resolve eq386 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq395 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq406 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq395 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq395
    | exact resolve eq395 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq412 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq395 x y
       grind)
    | exact superpose eq395 eq16
    | exact resolve eq16 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq476 : ∀ X0 X1 X2 X3 : G, (k (σ X1) X0) = (σ (k X1 (k (τ X0) (σ (M.op X2 (M.op X3 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X0 (σ (M.op X2 (M.op X3 (M.op X2 X3)))) X1
       have i₂ := eq170 X0 X2 X3
       grind)
    | exact superpose eq170 eq22
    | exact resolve eq22 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq485 : ∀ X0 X1 X2 X3 : G, (k (σ X1) X0) = (M.op (σ X1) (k X0 (σ (σ (M.op X2 (M.op X3 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq476 X0 X1 X2 X3
       have i₂ := eq406 X0 (σ (M.op X2 (M.op X3 (M.op X2 X3)))) X1
       grind)
    | exact superpose eq406 eq476
    | exact resolve eq476 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq476
  have eq498 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X1 x x
       have i₂ := eq170 X0 x x
       grind)
    | exact superpose eq170 eq485
    | exact resolve eq485 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq485
  have eq514 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq498
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq574 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq412
       have i₂ := eq514 x y
       grind)
    | exact superpose eq514 eq412
    | exact resolve eq412 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq514
  have eq575 : False := by grind
  exact eq575

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  clear eq25
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23 eq37
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq14436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14436
    | exact resolve eq14436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14436
  have eq14448 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14437
       have r₂ := eq28
       grind)
    | exact resolve eq14437 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14437
  have eq14450 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14448
    | exact resolve eq14448 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448
  have eq14457 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14450 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14450
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14450
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14450
       grind)
    | exact resolve eq12 eq14450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14450
  have eq14477 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq14457
  have eq14488 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14477
       have r₂ := eq27
       grind)
    | exact resolve eq14477 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14477
  have eq14498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14488 eq100
    | exact resolve eq100 eq14488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14488
  have eq14507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq14498
  have eq14510 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq14507
       have r₂ := eq28
       grind)
    | exact resolve eq14507 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14507
  have eq14521 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq14510
  have eq14555 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq27 eq14521
    | exact resolve eq14521 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14521
  have eq14566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq14555 eq100
    | exact resolve eq100 eq14555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq14555
  have eq14574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq14566
  have eq14576 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14574
       have r₂ := eq28
       grind)
    | exact resolve eq14574 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14574
  have eq14585 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14576
       grind)
    | exact superpose eq14576 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14576
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14576
       grind)
    | exact resolve eq12 eq14576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14576
  have eq14603 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq14585
  have eq14613 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14603
       have r₂ := eq19
       grind)
    | exact resolve eq14603 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14603
  have eq14618 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq14613
       grind)
    | exact superpose eq14613 eq77
    | exact resolve eq77 eq14613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14613
  have eq14638 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq14618
    | exact resolve eq14618 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14618
  have eq14659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14638 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq14638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14659
    | exact resolve eq14659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14659
  have eq14675 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14664
       have r₂ := eq28
       grind)
    | exact resolve eq14664 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14664
  have eq14677 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14675
    | exact resolve eq14675 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14675
  have eq15275 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14677 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14677
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14677
       grind)
    | exact resolve eq12 eq14677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14677
  have eq15295 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq15275
  have eq15306 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15295
       have r₂ := eq27
       grind)
    | exact resolve eq15295 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15295
  have eq15337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15306 eq14638
    | exact resolve eq14638 eq15306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15306
  have eq15340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq15337
  have eq15351 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15340
       have r₂ := eq28
       grind)
    | exact resolve eq15340 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15340
  have eq15356 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq15351
  have eq15390 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15356
    | exact resolve eq15356 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15356
  have eq15424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15390 eq14638
    | exact resolve eq14638 eq15390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14638 eq15390
  have eq15426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq15424
  have eq15436 : y = (M.op x x) := by
    first
    | (have r₁ := eq15426
       have r₂ := eq28
       grind)
    | exact resolve eq15426 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15426
  have eq15441 : (M.op x y) = (k y x) := by grind
  clear eq15436
  have eq15476 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq15441
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15441
    | exact resolve eq15441 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15441
  have eq15485 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq15476
       grind)
    | exact superpose eq15476 eq77
    | exact resolve eq77 eq15476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq15476
  have eq15503 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq15485
    | exact resolve eq15485 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq15485
  have eq15710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15503 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq15710
    | exact resolve eq15710 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15710
  have eq15722 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq15711
       have r₂ := eq28
       grind)
    | exact resolve eq15711 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15711
  have eq15724 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq15722
    | exact resolve eq15722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15722
  have eq20713 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15724 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15724
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15724
       grind)
    | exact resolve eq12 eq15724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15724
  have eq20735 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq20713
  have eq20752 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq20735
       have r₂ := eq27
       grind)
    | exact resolve eq20735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20735
  have eq20764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15503 eq20752
    | exact resolve eq20752 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20752
  have eq20769 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq20764
       have r₂ := eq28
       grind)
    | exact resolve eq20764 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20764
  have eq20975 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq20769
  have eq21021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15503 eq20975
    | exact resolve eq20975 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15503 eq20975
  have eq21041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq21021
    | exact resolve eq21021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21021
  have eq21049 : False := by grind
  exact eq21049

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation4521 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq77 : y ≠ (M.op x y) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq94
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq108
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108
    | exact resolve eq108 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq2361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2361
    | exact resolve eq2361 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361
  have eq2365 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2362
       have r₂ := eq28
       grind)
    | exact resolve eq2362 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2367 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2365
    | exact resolve eq2365 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2369 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2367 eq28
    | exact resolve eq28 eq2367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2370 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2367 eq78
    | (have r₁ := eq78
       have r₂ := eq2367
       grind)
    | exact resolve eq78 eq2367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq2367
  have eq2380 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2370
  have eq2381 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2380
  have eq2386 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2381 eq109
    | exact resolve eq109 eq2381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq2381
  have eq2390 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2386
  have eq2395 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2390
       have r₂ := eq2369
       grind)
    | exact resolve eq2390 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369 eq2390
  have eq2400 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq2395 eq30
    | exact resolve eq30 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq2421 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2400
    | exact resolve eq2400 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400
  have eq2422 : y = (M.op x y) ∨ x = y := by grind
  clear eq2421
  have eq2426 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2422 eq21
    | exact resolve eq21 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2428 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq2422 eq77
    | (have r₁ := eq77
       have r₂ := eq2422
       grind)
    | exact resolve eq77 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2422
  have eq2450 : y ≠ y ∨ x = y ∨ y = (k y x) := by grind
  clear eq2428
  have eq2451 : y = (k y x) ∨ x = y := by grind
  clear eq2450
  have eq2464 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2426
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2426
    | exact resolve eq2426 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2502 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq2451
       grind)
    | exact superpose eq2451 eq94
    | exact resolve eq94 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq2451
  have eq2507 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2502
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2502
    | exact resolve eq2502 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq2572 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2507 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2573 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2572
  have eq2579 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq2573
    | exact resolve eq2573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573
  have eq2997 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2579 eq28
    | exact resolve eq28 eq2579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq3015 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2997
       have r₂ := eq2464
       grind)
    | exact resolve eq2997 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464 eq2997
  have eq3018 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq3015 eq30
    | exact resolve eq30 eq3015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3015
  have eq3048 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq3018
    | exact resolve eq3018 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3018
  have eq3049 : x = y := by grind
  clear eq3048
  have eq3052 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3049
       grind)
    | exact superpose eq3049 eq19
    | exact resolve eq19 eq3049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3053 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3049
       grind)
    | exact superpose eq3049 eq25
    | exact resolve eq25 eq3049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3049
  have eq3069 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3053
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3053
    | exact resolve eq3053 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3053
  have eq3073 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3069 eq27
    | exact resolve eq27 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3069
  have eq3129 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3073 eq74
    | exact resolve eq74 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq3073
  have eq3156 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3129
       have i₂ := eq3052
       grind)
    | exact superpose eq3052 eq3129
    | exact resolve eq3129 eq3052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052 eq3129
  have eq3160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3156 eq15
    | exact resolve eq15 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq3160
    | exact resolve eq3160 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3160
  have eq3187 : False := by grind
  exact eq3187
