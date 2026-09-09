import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pyx_y_pyx_Equation3997 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : x ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) := by
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
  have eq82 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq96
    | exact resolve eq96 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq100 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq98
    | exact resolve eq98 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq98
  have eq111 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq89 y x
       grind)
    | exact superpose eq89 eq95
    | (have j1 := eq89 y x
       grind)
    | exact resolve eq95 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq127
    | exact resolve eq127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq135 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq89 (σ X0) sF2
       grind)
    | exact superpose eq89 eq39
    | (have j1 := eq89 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq89
    | (have j0 := eq89 (σ y) (σ x)
       grind)
    | exact resolve eq89 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq199
    | exact resolve eq199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq203 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq200
       have r₂ := eq27
       grind)
    | exact resolve eq200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq203
    | exact resolve eq203 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq207 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq27
    | exact resolve eq27 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1397 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq82
    | (have r₁ := eq82
       have r₂ := eq205
       grind)
    | exact resolve eq82 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq205
  have eq1398 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1397
  have eq1403 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1398 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1398
       grind)
    | exact resolve eq13 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq2453 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq1403 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq2456 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2453
    | exact resolve eq2453 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453
  have eq2458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq2456
    | exact resolve eq2456 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq2456
  have eq2466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2458
  have eq2469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2466
       have r₂ := eq207
       grind)
    | exact resolve eq2466 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq2466
  have eq2470 : x = (M.op x y) := by
    first
    | (have r₁ := eq2469
       have r₂ := eq27
       grind)
    | exact resolve eq2469 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469
  have eq2471 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2470 eq20
    | exact resolve eq20 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2474 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k y x) := by
    first
    | exact superpose eq2470 eq81
    | (have r₁ := eq81
       have r₂ := eq2470
       grind)
    | exact resolve eq81 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2479 : (M.op y x) = (M.op y y) ∨ x = (k y x) := by grind
  clear eq2474
  have eq2485 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2471
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2471
    | exact resolve eq2471 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq2488 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2485 eq26
    | exact resolve eq26 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3601 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq2479
       grind)
    | exact superpose eq2479 eq100
    | exact resolve eq100 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2479
  have eq4880 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2485 eq193
    | (have j0 := eq193 X0
       grind)
    | exact resolve eq193 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq4881 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq2485 eq4880
    | (have j0 := eq4880 X0
       grind)
    | exact resolve eq4880 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4880
  have eq4929 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq4881 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4881
    | (have j0 := eq4881 y
       grind)
    | exact resolve eq4881 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4881
  have eq4944 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2488 eq4929
    | exact resolve eq4929 eq2488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4929
  have eq4962 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq4944
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq4944
    | exact resolve eq4944 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq4944
  have eq4975 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2485 eq4962
    | exact resolve eq4962 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4962
  have eq4986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2488 eq4975
    | exact resolve eq4975 eq2488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488 eq4975
  have eq4991 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq4986
       have r₂ := eq27
       grind)
    | exact resolve eq4986 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4986
  have eq5001 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4991 eq111
    | exact resolve eq111 eq4991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq4991
  have eq5007 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2470 eq5001
    | exact resolve eq5001 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5001
  have eq5685 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3601
       have i₂ := eq5007
       grind)
    | exact superpose eq5007 eq3601
    | exact resolve eq3601 eq5007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601
  have eq5688 : (M.op y x) = (τ (M.op (σ y) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq5685
       grind)
    | exact superpose eq5685 eq16
    | exact resolve eq16 eq5685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5685
  have eq5711 : (M.op y x) = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq135 eq5688
    | exact resolve eq5688 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq5688
  have eq5728 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k y X0) = (M.op X0 y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq5711
       grind)
    | exact superpose eq5711 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5711
       grind)
    | exact resolve eq13 eq5711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5711
  have eq312939 : (M.op x y) = (k y x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq5728 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5728
  have eq312943 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq312939
       have i₂ := eq5007
       grind)
    | exact superpose eq5007 eq312939
    | exact resolve eq312939 eq5007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5007 eq312939
  have eq312947 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq312943
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq312943
    | exact resolve eq312943 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq312943
  have eq312948 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2470 eq312947
    | exact resolve eq312947 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470 eq312947
  have eq312949 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq312948
  have eq312991 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq312949 eq15
    | exact resolve eq15 eq312949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312949
  have eq313342 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq312991
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq312991
    | exact resolve eq312991 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq312991
  have eq313386 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2485 eq313342
    | exact resolve eq313342 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485 eq313342
  have eq313391 : False := by grind
  exact eq313391

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq11 eq13
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq176 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) x X2
       have i₂ := eq16 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq28 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 (M.op (M.op X1 X1) X2)) ∨ (M.op X0 X0) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X1 (k X0 (M.op (M.op X1 X1) X2))
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq532 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq532 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq541 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq536
       grind)
    | exact superpose eq536 eq40
    | exact resolve eq40 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq541
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq541
    | exact resolve eq541 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq544 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq542
    | exact resolve eq542 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq551 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq538 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq538
    | (have j0 := eq538 (σ X0)
       grind)
    | exact resolve eq538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq544 eq537
    | exact resolve eq537 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq554
       have r₂ := eq27
       grind)
    | exact resolve eq554 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq565 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq561
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq561
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq561 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq561 eq16
    | exact resolve eq16 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq561 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq568 eq565
    | exact resolve eq565 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq573 : ∀ X1 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X1) ∨ x = (M.op y y) := by
    intro X1
    first
    | exact superpose eq567 eq16
    | exact resolve eq16 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq573 eq26
    | (have j1 := eq573 (σ y)
       grind)
    | exact resolve eq26 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq589 eq573
    | exact resolve eq573 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq589
  have eq604 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq598 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq684 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq568 eq116
    | exact resolve eq116 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq690 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq684
    | exact resolve eq684 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq713 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq28 X0 X0
       grind)
    | (have r₁ := eq12 X0 (k X0 X0)
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq561 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq561
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq561
       grind)
    | exact resolve eq12 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq723
    | (have j0 := eq723 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq723 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq726 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq713 X0 X1
       have j1 := eq538 X0
       grind)
    | (have r₁ := eq713 X0 (M.op (k X0 X0) (k X0 X0))
       have r₂ := eq538 (k X0 X0)
       grind)
    | (have r₁ := eq713 X0 X1
       have r₂ := eq538 X0
       grind)
    | (have r₁ := eq713 X0 X0
       have r₂ := eq538 X0
       grind)
    | exact resolve eq713 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq727 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq539 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq539
    | (have j0 := eq539 (σ X0) X1
       grind)
    | exact resolve eq539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq569 eq116
    | exact resolve eq116 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq733
    | exact resolve eq733 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq754 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq741 eq604
    | exact resolve eq604 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq760 : x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq754
  have eq877 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq721 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq881 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq877 eq544
    | exact resolve eq544 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq877 eq142
    | exact resolve eq142 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq881
  have eq891 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq886
    | exact resolve eq886 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq894 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq536 eq891
    | exact resolve eq891 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq901 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq888
       grind)
    | exact superpose eq888 eq16
    | exact resolve eq16 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq907 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq894
       grind)
    | exact superpose eq894 eq16
    | exact resolve eq16 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq910 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq901 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq901
    | (have j0 := eq901 y X0
       grind)
    | exact resolve eq901 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq923 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq907 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq907
    | (have j0 := eq907 y X0
       grind)
    | exact resolve eq907 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq926 : ∀ X1 : G, (M.op x x) = (M.op x X1) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq16 x x X1
       have i₂ := eq907 x x
       grind)
    | exact superpose eq907 eq16
    | exact resolve eq16 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq923 eq12
    | (have j0 := eq12 (M.op x y) X0
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq923 (M.op x y)
       grind)
    | exact resolve eq12 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 : G, x = (k X0 (M.op x y)) ∨ (M.op X0 X0) = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq923 eq28
    | (have j0 := eq28 X0 (M.op x y)
       grind)
    | exact resolve eq28 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq994 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq926 X0
       have i₂ := eq28 x x
       grind)
    | exact superpose eq28 eq926
    | (have j1 := eq28 x x
       grind)
    | exact resolve eq926 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq926 y
       grind)
    | exact superpose eq926 eq18
    | (have j1 := eq926 y
       grind)
    | exact resolve eq18 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1007 eq994
    | (have j0 := eq994 X0
       grind)
    | exact resolve eq994 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1030 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq926 X0
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq926
    | exact resolve eq926 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k x X0) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq13
    | (have j0 := eq13 x X0
       grind)
    | exact resolve eq13 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1037 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq28
    | exact resolve eq28 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1030 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1290 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq724 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq724
    | (have j0 := eq724 (σ X0)
       grind)
    | exact resolve eq724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1293 : y = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq724 y
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq724
    | (have j0 := eq724 y
       grind)
    | exact resolve eq724 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1294 : y = (k y x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq724 y
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq724
    | (have j0 := eq724 y
       grind)
    | exact resolve eq724 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq1298 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq569 eq724
    | (have j0 := eq724 (σ y)
       grind)
    | exact resolve eq724 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq1304 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq38 (k sF0 sF0)
       have i₂ := eq724 sF0
       grind)
    | exact superpose eq724 eq38
    | (have j1 := eq724 (M.op x y)
       grind)
    | exact resolve eq38 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1314 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42 eq1304
    | exact resolve eq1304 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1319 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq877 eq1298
    | exact resolve eq1298 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1320 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq1319
  have eq1323 : y = (k y x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1294
       have r₂ := eq12 y y
       grind)
    | (have r₁ := eq1294
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1294 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1324 : y = (k y x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1293
       have r₂ := eq12 y y
       grind)
    | (have r₁ := eq1293
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1293 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1326 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1290 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq1290
    | (have j0 := eq1290 X0
       grind)
    | exact resolve eq1290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1331 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq1314
    | exact resolve eq1314 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1336 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq544 eq1320
    | exact resolve eq1320 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1344 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 x
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq176
    | (have j1 := eq28 (k X0 X0) (M.op (k X0 X0) X1)
       grind)
    | exact resolve eq176 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1373 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq176 X0 X2
       grind)
    | (have i₁ := eq176 X0 X2
       have i₂ := eq176 X0 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1393 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 x (M.op X0 X0)
       have i₂ := eq176 X0 x
       grind)
    | (have i₁ := eq28 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 X0 x
       grind)
    | exact superpose eq176 eq28
    | (have j0 := eq28 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq28 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1421 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1336 eq604
    | exact resolve eq604 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq1422 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1336 eq567
    | exact resolve eq567 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq1424 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1336 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq1336
       grind)
    | exact resolve eq13 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1426 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1424 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq1427 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1428 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1421
  have eq1439 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq176 y x
       have i₂ := eq1428
       grind)
    | exact superpose eq1428 eq176
    | exact resolve eq176 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1442 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq1428
       grind)
    | exact superpose eq1428 eq16
    | exact resolve eq16 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1447 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq1323
       grind)
    | exact superpose eq1323 eq37
    | exact resolve eq37 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1448 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1323
       grind)
    | exact superpose eq1323 eq40
    | exact resolve eq40 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1449 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1448
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1448
    | exact resolve eq1448 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1450 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1447
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1447
    | exact resolve eq1447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq1451 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq877 eq1449
    | exact resolve eq1449 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq1449
  have eq1452 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1450
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1450
    | exact resolve eq1450 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq1453 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1451 eq1452
    | exact resolve eq1452 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1458 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1451 eq537
    | exact resolve eq537 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1462 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1451 eq142
    | exact resolve eq142 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1463 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32 eq1462
    | exact resolve eq1462 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1513 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1453 eq537
    | exact resolve eq537 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1517 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1453 eq142
    | exact resolve eq142 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453
  have eq1518 : y = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32 eq1517
    | exact resolve eq1517 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1530 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq536
       have i₂ := eq1324
       grind)
    | exact superpose eq1324 eq536
    | exact resolve eq536 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1532 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1324
       grind)
    | exact superpose eq1324 eq40
    | exact resolve eq40 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1533 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1532
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1532
    | exact resolve eq1532 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq1570 : ∀ X0 X1 : G, x ≠ (M.op x X0) ∨ (k x X1) = (M.op X1 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq13 x X1
       have i₂ := eq1439 X0
       grind)
    | (have i₁ := eq13 x X1
       have i₂ := eq1439 x
       grind)
    | exact superpose eq1439 eq13
    | (have j0 := eq13 x X1
       grind)
    | exact resolve eq13 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1572 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq28 x x
       have i₂ := eq1439 X0
       grind)
    | (have i₁ := eq28 X0 x
       have i₂ := eq1439 X0
       grind)
    | exact superpose eq1439 eq28
    | exact resolve eq28 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1573 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1439 y
       grind)
    | exact superpose eq1439 eq18
    | (have j1 := eq1439 y
       grind)
    | exact resolve eq18 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1613 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1439 X0
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq1439
    | exact resolve eq1439 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1622 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq176 x x
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq176
    | exact resolve eq176 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1626 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq28
    | exact resolve eq28 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1631 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq1694 : ∀ X1 : G, x = (M.op (M.op x y) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq1442 x X1
       have i₂ := eq1631 x
       grind)
    | (have i₁ := eq1442 y X1
       have i₂ := eq1631 x
       grind)
    | exact superpose eq1631 eq1442
    | (have j0 := eq1442 y X1
       grind)
    | exact resolve eq1442 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1703 : ∀ X0 X1 : G, x ≠ X1 ∨ x = (M.op x X0) ∨ (M.op x X0) = (k (M.op x X0) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op x X0) X1
       have i₂ := eq1442 X0 (M.op x X0)
       grind)
    | exact superpose eq1442 eq12
    | (have j0 := eq12 (M.op x X0) X1
       grind)
    | (have r₁ := eq12 (M.op x X0) x
       have r₂ := eq1442 X0 (M.op x X0)
       grind)
    | exact resolve eq12 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq1707 : ∀ X1 : G, x = (M.op (M.op x y) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have j0 := eq1694 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1719 : ∀ X0 X1 : G, x ≠ X1 ∨ x = (M.op x X0) ∨ (k x x) = (k (k x x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq1572 eq1703
    | (have j0 := eq1703 X0 X1
       have j1 := eq1572 X0
       grind)
    | (have r₁ := eq1703 X0 (M.op x X0)
       have r₂ := eq1572 X0
       grind)
    | exact resolve eq1703 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572 eq1703
  have eq1724 : ∀ X1 : G, x ≠ X1 ∨ x = (M.op x y) ∨ (k x x) = (k (k x x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq1631 eq1719
    | (have j0 := eq1719 y X1
       grind)
    | exact resolve eq1719 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631 eq1719
  have eq1726 : ∀ X1 : G, x ≠ X1 ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq1626 eq1724
    | (have j0 := eq1724 X1
       grind)
    | (have r₁ := eq1724 (M.op x y)
       have r₂ := eq1626
       grind)
    | exact resolve eq1724 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq1724
  have eq1737 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1533 eq537
    | exact resolve eq537 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1744 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq561 eq1737
    | exact resolve eq1737 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq1910 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1622 eq28
    | exact resolve eq28 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq1925 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1707 eq1910
    | (have j0 := eq1910 X0
       grind)
    | exact resolve eq1910 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910
  have eq1981 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1458 eq176
    | exact resolve eq176 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1984 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq1458 eq16
    | exact resolve eq16 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1985 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1458 eq28
    | exact resolve eq28 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1986 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1985
  have eq2019 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1986 eq116
    | exact resolve eq116 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq2027 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30 eq2019
    | exact resolve eq2019 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2046 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1037
       grind)
    | exact superpose eq1037 eq40
    | exact resolve eq40 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2047 : x = (k x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq724 x
       have i₂ := eq1037
       grind)
    | exact superpose eq1037 eq724
    | (have j0 := eq724 x
       grind)
    | exact resolve eq724 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq2050 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq935 eq2047
    | (have j1 := eq935 x
       grind)
    | exact resolve eq2047 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq2051 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2050
  have eq2052 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2046
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2046
    | exact resolve eq2046 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046
  have eq2054 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2052
    | exact resolve eq2052 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2098 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 y X1 x
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq533
    | (have j0 := eq533 y X1 x
       grind)
    | exact resolve eq533 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2126 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28 eq2098
    | (have j0 := eq2098 X0 X1
       have j1 := eq28 y y
       grind)
    | exact resolve eq2098 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2132 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq760 eq2126
    | (have j0 := eq2126 X0 X1
       grind)
    | exact resolve eq2126 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2157 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq533 y X1 x
       have i₂ := eq2027
       grind)
    | exact superpose eq2027 eq533
    | (have j0 := eq533 y X1 x
       grind)
    | exact resolve eq533 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2163 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq907 eq2157
    | (have j0 := eq2157 X0 X1
       have j1 := eq907 X0 X1
       grind)
    | exact resolve eq2157 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157
  have eq2166 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq907 eq2163
    | (have j0 := eq2163 X0 X1
       have j1 := eq907 X0 X1
       grind)
    | exact resolve eq2163 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq2187 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1744 eq176
    | exact resolve eq176 eq1744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq2447 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1426 eq1427
    | exact resolve eq1427 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq2450 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2447
  have eq2540 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2450 eq142
    | exact resolve eq142 eq2450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2559 : x = (k x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq2540
    | exact resolve eq2540 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq2575 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq539 x X0
       have i₂ := eq2559
       grind)
    | exact superpose eq2559 eq539
    | (have j0 := eq539 x X0
       grind)
    | (have r₁ := eq539 x x
       have r₂ := eq2559
       grind)
    | exact resolve eq539 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq2576 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq538 x
       have i₂ := eq2559
       grind)
    | exact superpose eq2559 eq538
    | (have j0 := eq538 x
       grind)
    | (have r₁ := eq538 x
       have r₂ := eq2559
       grind)
    | exact resolve eq538 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq2577 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2576
  have eq2578 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575
  have eq2590 : x = (k y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2577
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq2577
    | (have j1 := eq28 x x
       grind)
    | exact resolve eq2577 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2592 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq176 y x
       have i₂ := eq2577
       grind)
    | exact superpose eq2577 eq176
    | exact resolve eq176 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2593 : ∀ X0 : G, x ≠ X0 ∨ x = y ∨ y = (k y X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2577
       grind)
    | exact superpose eq2577 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2577
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq2577
       grind)
    | exact resolve eq12 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2595 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq2577
       grind)
    | exact superpose eq2577 eq16
    | exact resolve eq16 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2596 : x = (k y y) ∨ x = y ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq2577
       grind)
    | exact superpose eq2577 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2597 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq28 eq2592
    | (have j1 := eq28 x x
       grind)
    | exact resolve eq2592 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq2598 : x = (k y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2596 eq2590
    | exact resolve eq2590 eq2596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590 eq2596
  have eq2599 : x = (k y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2598
  have eq2603 : ∀ X0 : G, x ≠ X0 ∨ y = (k y X0) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq726 y X0
       have i₂ := eq2599
       grind)
    | exact superpose eq2599 eq726
    | (have j0 := eq726 y X0
       grind)
    | (have r₁ := eq726 y x
       have r₂ := eq2599
       grind)
    | exact resolve eq726 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq2599
  have eq2609 : ∀ X0 : G, x ≠ X0 ∨ y = (k y X0) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2593 eq2603
    | (have j0 := eq2603 X0
       have j1 := eq2593 X0
       grind)
    | (have r₁ := eq2603 y
       have r₂ := eq2593 X0
       grind)
    | (have r₁ := eq2603 (M.op x x)
       have r₂ := eq2593 X0
       grind)
    | (have r₁ := eq2603 X0
       have r₂ := eq2593 (M.op x x)
       grind)
    | exact resolve eq2603 eq2593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2593 eq2603
  have eq2610 : ∀ X0 : G, x ≠ X0 ∨ y = (k y X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2609
  have eq2680 : ∀ X0 : G, (M.op (k x x) X0) = (M.op (k x x) (k x x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq176 x x
       have i₂ := eq2578 x
       grind)
    | exact superpose eq2578 eq176
    | exact resolve eq176 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2683 : ∀ X0 X1 : G, (k x x) = (M.op (M.op (k x x) X0) X1) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X1 x
       have i₂ := eq2578 x
       grind)
    | exact superpose eq2578 eq16
    | exact resolve eq16 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2784 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2559 eq2683
    | exact resolve eq2683 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2786 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2559 eq2680
    | exact resolve eq2680 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2680
  have eq2798 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2577 eq2786
    | exact resolve eq2786 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786
  have eq2813 : ∀ X0 X1 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x X1) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq176 y x
       have i₂ := eq2798 X0
       grind)
    | exact superpose eq2798 eq176
    | (have j1 := eq2798 X1
       grind)
    | exact resolve eq176 eq2798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2824 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2595 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2595
    | (have j0 := eq2595 y X0
       grind)
    | exact resolve eq2595 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595
  have eq2890 : ∀ X0 X1 : G, (k x x) = (k X0 (M.op (k x x) X1)) ∨ (M.op X0 X0) = (M.op (k x x) X1) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 x x
       have i₂ := eq2578 x
       grind)
    | exact superpose eq2578 eq535
    | exact resolve eq535 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq2891 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (k X2 (M.op (M.op (M.op X0 X0) X1) X3)) ∨ (M.op X2 X2) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq535 X0 (M.op X0 X0) X2
       have i₂ := eq176 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq535 X0 (M.op X0 X0) X2
       have i₂ := eq176 X0 X2
       grind)
    | exact superpose eq176 eq535
    | exact resolve eq535 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq3001 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (k X2 (M.op X0 X0)) ∨ (M.op X2 X2) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2891 X0 X1 X2 X3
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq2891
    | (have j0 := eq2891 X0 X1 X2 X3
       grind)
    | exact resolve eq2891 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891
  have eq3002 : ∀ X0 X1 : G, x = (k X0 (M.op x X1)) ∨ (M.op X0 X0) = (M.op (k x x) X1) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2559 eq2890
    | (have j0 := eq2890 X0 X1
       grind)
    | exact resolve eq2890 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq3030 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k X2 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3001 X0 X1 X2 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq3001
    | (have j0 := eq3001 X0 X1 X2 x
       grind)
    | exact resolve eq3001 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq3031 : ∀ X0 X1 : G, x = (k X0 (M.op x X1)) ∨ (M.op X0 X0) = (M.op x X1) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2559 eq3002
    | (have j0 := eq3002 X0 X1
       grind)
    | exact resolve eq3002 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559 eq3002
  have eq3046 : ∀ X0 X1 : G, x = (k X0 x) ∨ (M.op X0 X0) = (M.op x X1) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2798 eq3031
    | (have j0 := eq3031 X0 X1
       grind)
    | exact resolve eq3031 eq2798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3031
  have eq3048 : ∀ X0 : G, x = (k X0 x) ∨ (M.op X0 X0) = x ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2798 eq3046
    | (have j0 := eq3046 X0 x
       grind)
    | exact resolve eq3046 eq2798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798 eq3046
  have eq3224 : (M.op x y) = (k x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2597 y
       grind)
    | exact superpose eq2597 eq18
    | (have j1 := eq2597 y
       grind)
    | exact resolve eq18 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597
  have eq3292 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X1) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq533 x X1 x
       have i₂ := eq3224
       grind)
    | exact superpose eq3224 eq533
    | (have j0 := eq533 x X1 x
       grind)
    | exact resolve eq533 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224
  have eq3300 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X1) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq3292 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3292
  have eq3303 : ∀ X1 : G, (M.op x y) = (M.op x X1) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq2824 eq3300
    | exact resolve eq3300 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824 eq3300
  have eq3419 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2784 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2784
    | (have j0 := eq2784 y X0
       grind)
    | exact resolve eq2784 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3519 : x = (k (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3419 eq1426
    | exact resolve eq1426 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3520 : x = (k (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq3519
  have eq3538 : (σ x) = (k (σ (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3520 eq42
    | exact resolve eq42 eq3520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520
  have eq3539 : (σ x) = (k (σ (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3538
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3538
    | exact resolve eq3538 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq3597 : ∀ X0 X1 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X1) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq2813 X0 X1
       have i₂ := eq28 x x
       grind)
    | exact superpose eq28 eq2813
    | (have j0 := eq2813 X0 X1
       have j1 := eq28 x x
       grind)
    | exact resolve eq2813 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3661 : ∀ X0 : G, x ≠ (M.op x x) ∨ x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2813 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813
  have eq3721 : ∀ X0 X1 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X1) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq3597 X0 X1
       have j1 := eq3661 X1
       grind)
    | (have r₁ := eq3597 X0 x
       have r₂ := eq3661 X0
       grind)
    | (have r₁ := eq3597 X0 X1
       have r₂ := eq3661 X0
       grind)
    | exact resolve eq3597 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597
  have eq3807 : ∀ X0 : G, x ≠ (M.op x y) ∨ x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3661 X0
       have i₂ := eq3303 x
       grind)
    | (have i₁ := eq3661 X0
       have i₂ := eq3303 x
       grind)
    | exact superpose eq3303 eq3661
    | (have j0 := eq3661 X0
       grind)
    | (have r₁ := eq3661 X0
       have r₂ := eq3303 x
       grind)
    | exact resolve eq3661 eq3303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303
  have eq3811 : ∀ X0 : G, x ≠ (M.op x y) ∨ x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq3807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3807
  have eq3826 : ∀ X0 : G, x ≠ (M.op x y) ∨ x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq3811 X0
       have j1 := eq3661 X0
       grind)
    | (have r₁ := eq3811 X0
       have r₂ := eq3661 y
       grind)
    | (have r₁ := eq3811 x
       have r₂ := eq3661 X0
       grind)
    | (have r₁ := eq3811 X0
       have r₂ := eq3661 X0
       grind)
    | exact resolve eq3811 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811
  have eq4823 : ∀ X1 : G, (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x X1) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq1439 x
       have i₂ := eq3721 x X1
       grind)
    | exact superpose eq3721 eq1439
    | (have j1 := eq3721 x X1
       grind)
    | exact resolve eq1439 eq3721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439 eq3721
  have eq4877 : ∀ X1 : G, (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x X1) := by
    intro X1
    first
    | (have j0 := eq4823 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4823
  have eq4918 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq1570 x x
       grind)
    | (have r₁ := eq4877 x
       have r₂ := eq1570 x x
       grind)
    | exact resolve eq4877 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570 eq4877
  have eq4930 : (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1573 eq4918
    | exact resolve eq4918 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573 eq4918
  have eq4945 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4930
       grind)
    | exact superpose eq4930 eq40
    | exact resolve eq40 eq4930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4930
  have eq4957 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4945
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4945
    | exact resolve eq4945 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4945
  have eq4959 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq4957
    | exact resolve eq4957 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957
  have eq5377 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq1513 eq16
    | exact resolve eq16 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5383 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq1513 eq1373
    | exact resolve eq1373 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5384 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1513 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq5385 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq5384
  have eq5453 : ∀ X0 : G, (σ x) = (k X0 (σ (M.op x y))) ∨ (M.op x y) = (M.op (τ X0) (τ X0)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq935 eq35
    | (have j1 := eq935 (τ X0)
       grind)
    | exact resolve eq35 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq935
  have eq5466 : ∀ X0 : G, (σ x) = (k X0 (σ (M.op x y))) ∨ (M.op x y) = (M.op (τ X0) (τ X0)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq5453
    | (have j0 := eq5453 X0
       grind)
    | exact resolve eq5453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5453
  have eq5470 : ∀ X0 : G, (M.op x y) = (M.op (τ X0) (τ X0)) ∨ (σ x) = (k X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5466 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5466
    | (have j0 := eq5466 X0
       grind)
    | exact resolve eq5466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5466
  have eq5678 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq926 x
       have i₂ := eq1026 x
       grind)
    | exact superpose eq1026 eq926
    | (have j1 := eq1026 x
       grind)
    | exact resolve eq926 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926 eq1026
  have eq5728 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5678
  have eq5756 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1035 x
       grind)
    | (have r₁ := eq5728
       have r₂ := eq1035 x
       grind)
    | exact resolve eq5728 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq5728
  have eq5774 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1007 eq5756
    | exact resolve eq5756 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5799 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq5774
       grind)
    | exact superpose eq5774 eq40
    | exact resolve eq40 eq5774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5802 : x = (k x (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq724 x
       have i₂ := eq5774
       grind)
    | exact superpose eq5774 eq724
    | (have j0 := eq724 x
       grind)
    | exact resolve eq724 eq5774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq5806 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2051 eq5802
    | exact resolve eq5802 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051 eq5802
  have eq5809 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5799
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5799
    | exact resolve eq5799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5799
  have eq5811 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq5809
    | exact resolve eq5809 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5809
  have eq5856 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1981 eq26
    | (have j1 := eq1981 (σ y)
       grind)
    | exact resolve eq26 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5908 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5856 eq1981
    | exact resolve eq1981 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981 eq5856
  have eq5928 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq5908 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5908
  have eq5984 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X1
    first
    | exact superpose eq5928 eq1984
    | (have j0 := eq1984 (σ y) X1
       grind)
    | exact resolve eq1984 eq5928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984
  have eq6014 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have j0 := eq5984 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5984
  have eq6175 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5385 eq116
    | exact resolve eq116 eq5385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq5385
  have eq6186 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq6175
    | exact resolve eq6175 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6175
  have eq6243 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1530
       grind)
    | exact superpose eq1530 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1530
       grind)
    | exact resolve eq13 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq6252 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6243 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6243
  have eq6617 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq533 y X1 x
       have i₂ := eq6186
       grind)
    | exact superpose eq6186 eq533
    | (have j0 := eq533 y X1 x
       grind)
    | exact resolve eq533 eq6186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq6186
  have eq6622 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq907 eq6617
    | (have j0 := eq6617 X0 X1
       have j1 := eq907 X0 X1
       grind)
    | exact resolve eq6617 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq6617
  have eq6625 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq2166 eq6622
    | (have j0 := eq6622 X0 X1
       have j1 := eq2166 X0 X1
       grind)
    | exact resolve eq6622 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166 eq6622
  have eq6626 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq6625 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6625
  have eq6789 : y = (k y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j0 := eq2610 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610
  have eq6790 : y = (k y x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1518 eq6789
    | exact resolve eq6789 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518 eq6789
  have eq6798 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq6790
       grind)
    | exact superpose eq6790 eq40
    | exact resolve eq40 eq6790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6790
  have eq6801 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq6798
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6798
    | exact resolve eq6798 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6798
  have eq6848 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5806 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq5806
       grind)
    | exact resolve eq13 eq5806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5806
  have eq6856 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6848 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6848
  have eq7141 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1925 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1925 (M.op x y)
       grind)
    | exact resolve eq13 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq7154 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq7141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7141
  have eq7306 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2187 eq26
    | (have j1 := eq2187 (σ y)
       grind)
    | exact resolve eq26 eq2187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7393 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7306 eq2187
    | exact resolve eq2187 eq7306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187
  have eq7412 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7306 eq28
    | exact resolve eq28 eq7306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7306
  have eq7413 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq7412
  have eq7420 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7393 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7393
  have eq9840 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq932 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq9844 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9840 eq40
    | exact resolve eq40 eq9840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9840
  have eq9845 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq9844
    | exact resolve eq9844 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9844
  have eq10476 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j0 := eq1726 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq10480 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10476 eq40
    | exact resolve eq40 eq10476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10481 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq10480
    | exact resolve eq10480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10480
  have eq12347 : ∀ X1 X2 : G, (M.op x X1) = (M.op x X2) ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq1373 (M.op x x) X1 X2
       have i₂ := eq2132 x (M.op x x)
       grind)
    | exact superpose eq2132 eq1373
    | exact resolve eq1373 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12400 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq5377
    | (have j0 := eq5377 (σ y) X0
       grind)
    | exact resolve eq5377 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5377
  have eq12630 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5383 eq26
    | (have j1 := eq5383 (σ y) X0
       grind)
    | exact resolve eq26 eq5383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5383
  have eq13873 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq536
       have i₂ := eq3048 y
       grind)
    | exact superpose eq3048 eq536
    | (have j1 := eq3048 y
       grind)
    | exact resolve eq536 eq3048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048
  have eq13909 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13873
  have eq14060 : ∀ X0 X1 : G, x = (k X0 (M.op x X1)) ∨ (M.op X0 X0) = (M.op x X1) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 y x
       have i₂ := eq13909
       grind)
    | exact superpose eq13909 eq535
    | exact resolve eq535 eq13909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq14062 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1373 y X1 x
       have i₂ := eq13909
       grind)
    | exact superpose eq13909 eq1373
    | exact resolve eq1373 eq13909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14395 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq14062 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq14062 X0 y
       grind)
    | exact superpose eq14062 eq18
    | (have j1 := eq14062 y X0
       grind)
    | exact resolve eq18 eq14062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14062
  have eq15722 : (M.op x y) = (M.op (k x x) (k x x)) ∨ (σ x) = (k (k (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98 eq5470
    | (have j0 := eq5470 (k (σ x) (σ x))
       grind)
    | exact resolve eq5470 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq5470
  have eq15752 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (k (k (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5774 eq15722
    | exact resolve eq15722 eq5774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5774 eq15722
  have eq15757 : x = (M.op x y) ∨ (σ x) = (k (k (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq923 eq15752
    | exact resolve eq15752 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15752
  have eq15759 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2054 eq15757
    | exact resolve eq15757 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15757
  have eq15760 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15759 eq134
    | exact resolve eq134 eq15759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq15759
  have eq15771 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq15760
    | exact resolve eq15760 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15760
  have eq15953 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq12347 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq12347 X0 y
       grind)
    | exact superpose eq12347 eq18
    | (have j1 := eq12347 y X0
       grind)
    | exact resolve eq18 eq12347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16810 : x ≠ (k y y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6252
  have eq16946 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16810
       have r₂ := eq760
       grind)
    | exact resolve eq16810 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq16810
  have eq17016 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq16946
       grind)
    | exact superpose eq16946 eq16
    | exact resolve eq16 eq16946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17022 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1373 y X1 x
       have i₂ := eq16946
       grind)
    | exact superpose eq16946 eq1373
    | exact resolve eq1373 eq16946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16946
  have eq17030 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17016 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17016
    | (have j0 := eq17016 y X0
       grind)
    | exact resolve eq17016 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17164 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17030 eq12
    | (have j0 := eq12 (M.op x y) X0
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq17030 (M.op x y)
       grind)
    | exact resolve eq12 eq17030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17371 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq17022 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq17022 X0 y
       grind)
    | exact superpose eq17022 eq18
    | (have j1 := eq17022 y X0
       grind)
    | exact resolve eq18 eq17022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17432 : ∀ X0 X1 : G, x ≠ (M.op x X0) ∨ (k x X1) = (M.op X1 x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 x X1
       have i₂ := eq17022 x X0
       grind)
    | (have i₁ := eq13 x X1
       have i₂ := eq17022 X0 x
       grind)
    | exact superpose eq17022 eq13
    | (have j0 := eq13 x X1
       grind)
    | exact resolve eq13 eq17022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17022
  have eq17687 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq17371 X0
       grind)
    | (have i₁ := eq28 y x
       have i₂ := eq17371 X0
       grind)
    | exact superpose eq17371 eq28
    | (have j0 := eq28 X0 x
       grind)
    | exact resolve eq28 eq17371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17821 : (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2450 eq551
    | (have j0 := eq551 (σ x)
       grind)
    | exact resolve eq551 eq2450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450
  have eq17857 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq17821
  have eq18094 : ∀ X0 : G, (σ (σ x)) ≠ (σ (σ x)) ∨ (k (σ (σ x)) X0) = (M.op X0 (σ (σ x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq17857 eq13
    | (have j0 := eq13 (σ (σ x)) X0
       grind)
    | (have r₁ := eq13 (σ (σ x)) x
       have r₂ := eq17857
       grind)
    | exact resolve eq13 eq17857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17857
  have eq18102 : ∀ X0 : G, (k (σ (σ x)) X0) = (M.op X0 (σ (σ x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq18094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18094
  have eq18223 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq17687 x
       grind)
    | exact superpose eq17687 eq36
    | (have j1 := eq17687 x
       grind)
    | exact resolve eq36 eq17687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17687
  have eq18279 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18223
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18223
    | exact resolve eq18223 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18223
  have eq18297 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18279
    | exact resolve eq18279 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18279
  have eq18305 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17371 eq18297
    | exact resolve eq18297 eq17371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18297
  have eq19915 : ∀ X0 : G, x = (M.op (k (σ (σ x)) x) X0) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq18102 eq2784
    | exact resolve eq2784 eq18102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19950 : x = (k (σ (σ x)) (M.op x y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18102 eq3419
    | exact resolve eq3419 eq18102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18102
  have eq20011 : x = (k (σ (σ x)) (M.op x y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq19950
  have eq20034 : ∀ X0 : G, x = (M.op (k (σ (σ x)) x) X0) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq19915 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19915
  have eq20150 : (M.op x y) = (k (σ (σ x)) (M.op x y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13909 eq20011
    | exact resolve eq20011 eq13909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20011
  have eq20151 : ∀ X0 : G, (M.op x y) = (M.op (k (σ (σ x)) (M.op x y)) X0) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq13909 eq20034
    | exact resolve eq20034 eq13909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20034
  have eq20198 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq20150 eq20151
    | exact resolve eq20151 eq20150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20150 eq20151
  have eq20281 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X1) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq20198 eq16
    | exact resolve eq16 eq20198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20293 : (M.op x y) = (k (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20198 eq1426
    | exact resolve eq1426 eq20198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426 eq20198
  have eq20294 : (M.op x y) = (k (σ x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq20293
  have eq20335 : ∀ X1 : G, (M.op x y) = (M.op x X1) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq3419 eq20281
    | exact resolve eq20281 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419 eq20281
  have eq20341 : ∀ X1 : G, (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x X1) ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | exact superpose eq14395 eq20335
    | (have j0 := eq20335 X1
       have j1 := eq14395 X1
       grind)
    | exact resolve eq20335 eq14395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20335
  have eq20356 : (σ (M.op x y)) = (k (σ (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20294 eq42
    | exact resolve eq42 eq20294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20294
  have eq20365 : (σ (M.op x y)) = (k (σ (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq20356
    | exact resolve eq20356 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20356
  have eq20367 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3539 eq20365
    | exact resolve eq20365 eq3539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539 eq20365
  have eq20374 : ∀ X0 : G, x ≠ X0 ∨ x = y ∨ y = (k y X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq20367
       grind)
    | exact superpose eq20367 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20367
       grind)
    | exact resolve eq12 eq20367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20383 : x = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq20367
       grind)
    | exact superpose eq20367 eq28
    | exact resolve eq28 eq20367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21392 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1326 y
       have i₂ := eq20383
       grind)
    | exact superpose eq20383 eq1326
    | (have j0 := eq1326 y
       grind)
    | exact resolve eq1326 eq20383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20383
  have eq21393 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21392
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq21392
    | exact resolve eq21392 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21392
  have eq21400 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21393
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21393
    | exact resolve eq21393 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21393
  have eq21405 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21400
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21400
    | exact resolve eq21400 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21400
  have eq21408 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1451 eq21405
    | exact resolve eq21405 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21405
  have eq21409 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1451 eq21408
    | exact resolve eq21408 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451 eq21408
  have eq21410 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq21409
  have eq22679 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21410 eq142
    | exact resolve eq142 eq21410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21410
  have eq22680 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32 eq22679
    | exact resolve eq22679 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22679
  have eq23297 : ∀ X0 : G, x = (k X0 (M.op x x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op X0 X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2784 x x
       have i₂ := eq3030 x x X0
       grind)
    | exact superpose eq3030 eq2784
    | (have j1 := eq3030 X0 x x
       grind)
    | exact resolve eq2784 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784 eq3030
  have eq23371 : ∀ X0 : G, x = (k X0 (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op X0 X0) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq14060 eq23297
    | (have j0 := eq23297 X0
       have j1 := eq14060 X0 x
       grind)
    | exact resolve eq23297 eq14060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14060 eq23297
  have eq23517 : ∀ X0 : G, x = (k X0 (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op X0 X0) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq20341 eq23371
    | (have j0 := eq23371 X0
       grind)
    | exact resolve eq23371 eq20341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23371
  have eq23551 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ x = (k X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20341 eq23517
    | (have j0 := eq23517 X0
       grind)
    | exact resolve eq23517 eq20341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20341 eq23517
  have eq24769 : x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j0 := eq20374 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20374
  have eq24770 : x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1463 eq24769
    | exact resolve eq24769 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463 eq24769
  have eq24771 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq24770
  have eq24780 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq536
       have i₂ := eq24771
       grind)
    | exact superpose eq24771 eq536
    | exact resolve eq536 eq24771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq24771
  have eq24837 : x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq24780
       grind)
    | exact superpose eq24780 eq28
    | exact resolve eq28 eq24780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24780
  have eq24838 : x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq24837
  have eq24848 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq24838
       grind)
    | exact superpose eq24838 eq41
    | exact resolve eq41 eq24838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24838
  have eq24863 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24848
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24848
    | exact resolve eq24848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24848
  have eq24868 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24863
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24863
    | exact resolve eq24863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24863
  have eq26634 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j0 := eq17164 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17164
  have eq28190 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6626 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6626
    | (have j0 := eq6626 y X0
       grind)
    | exact resolve eq6626 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6626
  have eq28363 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ x = (M.op (M.op x y) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28190 eq13
    | (have j0 := eq13 (M.op x y) X0
       have j1 := eq28190 X1
       grind)
    | (have r₁ := eq13 (M.op x y) X1
       have r₂ := eq28190 X0
       grind)
    | exact resolve eq13 eq28190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28370 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) X1) ∨ x = (M.op (M.op x y) X2) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq28190 eq1373
    | (have j1 := eq28190 X2
       grind)
    | exact resolve eq1373 eq28190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28375 : ∀ X0 X1 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ x = (M.op (M.op x y) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq28363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28363
  have eq28466 : (M.op x y) ≠ (M.op x y) ∨ x = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j0 := eq23551 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23551
  have eq28467 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by grind
  clear eq28466
  have eq28522 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq2577
       have i₂ := eq28467
       grind)
    | exact superpose eq28467 eq2577
    | exact resolve eq2577 eq28467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq28526 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq13909
       have i₂ := eq28467
       grind)
    | exact superpose eq28467 eq13909
    | exact resolve eq13909 eq28467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13909
  have eq28529 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq20367
       have i₂ := eq28467
       grind)
    | exact superpose eq28467 eq20367
    | exact resolve eq20367 eq28467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20367
  have eq28549 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq28467
       grind)
    | exact superpose eq28467 eq28
    | exact resolve eq28 eq28467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28467
  have eq28551 : x = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq28529
  have eq28553 : x = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq28526
  have eq28555 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by grind
  clear eq28522
  have eq28571 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | (have j1 := eq3826 x
       grind)
    | (have r₁ := eq28555
       have r₂ := eq3826 x
       grind)
    | exact resolve eq28555 eq3826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28555
  have eq28575 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq28553 eq28571
    | exact resolve eq28571 eq28553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28553 eq28571
  have eq28628 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28575 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq28575
       grind)
    | exact resolve eq13 eq28575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28575
  have eq28639 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq28628 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28628
  have eq31566 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1393 x x
       have i₂ := eq1041 x
       grind)
    | exact superpose eq1041 eq1393
    | exact resolve eq1393 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq31582 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (k (M.op x X0) (M.op x X0)) ∨ (M.op x X0) = (M.op (M.op x X0) X1) ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1393 x X1
       have i₂ := eq12347 x x
       grind)
    | (have i₁ := eq1393 x X1
       have i₂ := eq12347 X1 x
       grind)
    | exact superpose eq12347 eq1393
    | exact resolve eq1393 eq12347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12347
  have eq31589 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1393 x x
       have i₂ := eq17371 x
       grind)
    | exact superpose eq17371 eq1393
    | exact resolve eq1393 eq17371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31721 : ∀ X0 : G, x = (k (M.op x x) (M.op x x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq17016 x X0
       have i₂ := eq1393 x X0
       grind)
    | exact superpose eq1393 eq17016
    | (have j1 := eq1393 x X0
       grind)
    | exact resolve eq17016 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31791 : x = (k (M.op x x) (M.op x x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17016 eq31721
    | exact resolve eq31721 eq17016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17016 eq31721
  have eq31864 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17030 eq31589
    | (have j0 := eq31589 X0
       grind)
    | exact resolve eq31589 eq17030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31589
  have eq31871 : ∀ X0 X1 : G, x = (k (M.op x X0) (M.op x X0)) ∨ (M.op x X0) = (M.op (M.op x X0) X1) ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2132 eq31582
    | (have j0 := eq31582 X0 X1
       grind)
    | exact resolve eq31582 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31582
  have eq31885 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq923 eq31566
    | (have j0 := eq31566 X0
       grind)
    | exact resolve eq31566 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31566
  have eq31980 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17371 eq31791
    | exact resolve eq31791 eq17371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31791
  have eq32041 : ∀ X0 : G, x = (k (M.op x X0) (M.op x X0)) ∨ x = (M.op x X0) ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2132 eq31871
    | (have j0 := eq31871 X0 x
       grind)
    | exact resolve eq31871 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132 eq31871
  have eq32118 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17371 eq31980
    | exact resolve eq31980 eq17371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31980
  have eq32160 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x X0) ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq15953 eq32041
    | (have j0 := eq32041 y
       grind)
    | exact resolve eq32041 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32041
  have eq32212 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15953 eq32160
    | (have j0 := eq32160 y
       grind)
    | exact resolve eq32160 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15953 eq32160
  have eq32236 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32118 eq32212
    | exact resolve eq32212 eq32118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32212
  have eq32237 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32236
  have eq32250 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32118 eq32237
    | exact resolve eq32237 eq32118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32118 eq32237
  have eq32251 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32250
  have eq33221 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32251 eq42
    | exact resolve eq42 eq32251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33225 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32251 eq551
    | (have j0 := eq551 (M.op x y)
       grind)
    | exact resolve eq551 eq32251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33229 : (σ (M.op x y)) = (σ (k (M.op x y) x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32251 eq1326
    | (have j0 := eq1326 (M.op x y)
       grind)
    | exact resolve eq1326 eq32251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326 eq32251
  have eq33239 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33229
       have i₂ := eq40 sF0
       grind)
    | exact superpose eq40 eq33229
    | exact resolve eq33229 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33229
  have eq33241 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq33225
    | exact resolve eq33225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33225
  have eq33242 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq33221
    | exact resolve eq33221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33221
  have eq33246 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq33239
    | exact resolve eq33239 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33239
  have eq33248 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33241
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33241
    | exact resolve eq33241 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33241
  have eq33249 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33242
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33242
    | exact resolve eq33242 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33242
  have eq33252 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq33246
    | exact resolve eq33246 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33246
  have eq33254 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq33248
    | exact resolve eq33248 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33248
  have eq33255 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10481 eq33252
    | exact resolve eq33252 eq10481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10481 eq33252
  have eq33258 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33249 eq1331
    | exact resolve eq1331 eq33249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq33270 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq33249 eq1344
    | (have j0 := eq1344 (σ (M.op x y)) x
       grind)
    | exact resolve eq1344 eq33249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq34373 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq561 eq33255
    | exact resolve eq33255 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq33255
  have eq34428 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9845 eq34373
    | exact resolve eq34373 eq9845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9845 eq34373
  have eq34435 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33258 eq34428
    | exact resolve eq34428 eq33258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33258 eq34428
  have eq34436 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34435
  have eq34444 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34436 eq142
    | exact resolve eq142 eq34436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34436
  have eq34445 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq34444
    | exact resolve eq34444 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34444
  have eq34505 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq28549
       grind)
    | exact superpose eq28549 eq41
    | exact resolve eq41 eq28549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq28549
  have eq34546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq34505
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34505
    | exact resolve eq34505 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34505
  have eq34555 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq20 eq34546
    | exact resolve eq34546 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34546
  have eq37301 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq34555 eq24868
    | exact resolve eq24868 eq34555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24868 eq34555
  have eq37315 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by grind
  clear eq37301
  have eq37337 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq28551 eq37315
    | exact resolve eq37315 eq28551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28551 eq37315
  have eq37338 : x = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq37337
  have eq37376 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq37338 eq42
    | exact resolve eq42 eq37338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37338
  have eq37378 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37376
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37376
    | exact resolve eq37376 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37376
  have eq37380 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37378
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37378
    | exact resolve eq37378 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37378
  have eq48909 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6856 eq31885
    | exact resolve eq31885 eq6856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6856 eq31885
  have eq48984 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq48909
  have eq49140 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq15771 eq48984
    | exact resolve eq48984 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48984
  have eq49141 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq49140
  have eq49646 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq49141
  have eq49666 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq49646
       have r₂ := eq15771
       grind)
    | exact resolve eq49646 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771 eq49646
  have eq59932 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7154 eq1707
    | exact resolve eq1707 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq59943 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7154 eq17030
    | exact resolve eq17030 eq7154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7154 eq17030
  have eq60061 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59943
  have eq60071 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59932
  have eq60307 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq49666 eq60061
    | exact resolve eq60061 eq49666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49666 eq60061
  have eq60327 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq60071 eq42
    | exact resolve eq42 eq60071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60071
  have eq60359 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq60327
    | exact resolve eq60327 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60327
  have eq60367 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq60359
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60359
    | exact resolve eq60359 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60359
  have eq60420 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq60307 eq42
    | exact resolve eq42 eq60307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60307
  have eq60449 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq60420
    | exact resolve eq60420 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60420
  have eq60457 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq60449
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60449
    | exact resolve eq60449 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60449
  have eq63050 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X2) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq28370 eq28190
    | (have j0 := eq28190 X1
       have j1 := eq28370 X0 X1 X1
       grind)
    | exact resolve eq28190 eq28370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63094 : ∀ X0 X1 : G, x ≠ (M.op (M.op x y) X1) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq28370 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28370
  have eq63100 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63050 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63050
  have eq63187 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq63100 X0 X1 X1
       have j1 := eq63094 X1 X1
       grind)
    | (have r₁ := eq63100 X0 X1 x
       have r₂ := eq63094 X0 X1
       grind)
    | (have r₁ := eq63100 X0 X1 X1
       have r₂ := eq63094 X0 X1
       grind)
    | exact resolve eq63100 eq63094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63100
  have eq63335 : ∀ X0 X1 : G, x ≠ (M.op x y) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28190 eq63094
    | (have j0 := eq63094 X0 X1
       have j1 := eq28190 X0
       grind)
    | (have r₁ := eq63094 X0 X0
       have r₂ := eq28190 X0
       grind)
    | exact resolve eq63094 eq28190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28190
  have eq63360 : ∀ X0 X1 : G, x ≠ (M.op x y) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have j0 := eq63335 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63335
  have eq63388 : ∀ X0 : G, x ≠ (M.op x y) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq63360 X0 X0
       have j1 := eq63094 X0 x
       grind)
    | (have r₁ := eq63360 x x
       have r₂ := eq63094 X0 x
       grind)
    | (have r₁ := eq63360 X0 x
       have r₂ := eq63094 X0 x
       grind)
    | exact resolve eq63360 eq63094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63360
  have eq63957 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28375 eq63187
    | (have j0 := eq63187 X0 X0
       have j1 := eq28375 X0 X0
       grind)
    | exact resolve eq63187 eq28375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28375
  have eq64038 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have j0 := eq63957 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63957
  have eq64185 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq64038 X0 X0
       have j1 := eq63094 X0 x
       grind)
    | (have r₁ := eq64038 x x
       have r₂ := eq63094 X0 x
       grind)
    | (have r₁ := eq64038 X0 x
       have r₂ := eq63094 X0 x
       grind)
    | exact resolve eq64038 eq63094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63094 eq64038
  have eq65409 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq64185 eq551
    | (have j0 := eq551 (M.op x y)
       have j1 := eq64185 X0
       grind)
    | exact resolve eq551 eq64185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64185
  have eq65423 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq65409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65409
  have eq65466 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq65423
    | (have j0 := eq65423 X0
       grind)
    | exact resolve eq65423 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65423
  have eq65493 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq910 eq65466
    | (have j0 := eq65466 X0
       have j1 := eq910 X0
       grind)
    | exact resolve eq65466 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910 eq65466
  have eq67314 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq65493 eq1458
    | (have j1 := eq65493 X0
       grind)
    | exact resolve eq1458 eq65493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458 eq65493
  have eq67348 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq67314 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67314
  have eq67366 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq923 eq67348
    | (have j0 := eq67348 X0
       have j1 := eq923 X0
       grind)
    | exact resolve eq67348 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq67348
  have eq67379 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq67366 X0
       have j1 := eq63388 X0
       grind)
    | (have r₁ := eq67366 X0
       have r₂ := eq63388 X0
       grind)
    | exact resolve eq67366 eq63388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63388 eq67366
  have eq67495 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f67495_14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
      intro X0 X1 X2
      grind
    have f67495_15 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) := by
      intro X0
      grind
    have f67495_24 : (M.op x X0) ≠ (M.op x X1) := by grind
    have f67495_25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f67495_26 : (σ y) ≠ (σ x) := by grind
    have f67495_29 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ y) = (σ x) := by
      intro X0
      first
      | (have j0 := f67495_15 X0
         grind)
      | (have r₁ := f67495_15 X0
         have r₂ := f67495_25
         grind)
      | exact resolve f67495_15 f67495_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f67495_30 : ∀ X0 : G, x = (M.op (M.op x y) X0) := by
      intro X0
      first
      | (have j0 := f67495_29 X0
         grind)
      | (have r₁ := f67495_29 X0
         have r₂ := f67495_26
         grind)
      | exact resolve f67495_29 f67495_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f67495_39 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
      intro X0 X1
      first
      | (have i₁ := f67495_14 (M.op x y) X1 x
         have i₂ := f67495_30 (M.op x y)
         grind)
      | exact superpose f67495_30 f67495_14
      | exact resolve f67495_14 f67495_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f67495_53 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) := by
      intro X0
      first
      | (have i₁ := f67495_24
         have i₂ := f67495_39 X1 X0
         grind)
      | (have i₁ := f67495_24
         have i₂ := f67495_39 X0 X1
         grind)
      | exact superpose f67495_39 f67495_24
      | (have r₁ := f67495_24
         have r₂ := f67495_39 X0 X1
         grind)
      | (have r₁ := f67495_24
         have r₂ := f67495_39 X1 X0
         grind)
      | exact resolve f67495_24 f67495_39
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f67495_56 : False := by
      first
      | (have r₁ := f67495_53 x
         have r₂ := f67495_39 X0 x
         grind)
      | (have r₁ := f67495_53 x
         have r₂ := f67495_39 x X0
         grind)
      | exact resolve f67495_53 f67495_39
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f67495_56
  have eq68149 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq67495 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq67495 X0 y
       grind)
    | exact superpose eq67495 eq18
    | (have j1 := eq67495 y X0
       grind)
    | exact resolve eq18 eq67495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68728 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ (M.op X0 X0) = x ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq68149 X0
       grind)
    | (have i₁ := eq28 y x
       have i₂ := eq68149 X0
       grind)
    | exact superpose eq68149 eq28
    | (have j0 := eq28 X0 x
       grind)
    | exact resolve eq28 eq68149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70237 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq68728 x
       grind)
    | exact superpose eq68728 eq36
    | (have j1 := eq68728 x
       grind)
    | exact resolve eq36 eq68728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq68728
  have eq70298 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70237
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70237
    | exact resolve eq70237 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70237
  have eq70335 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq70298
    | exact resolve eq70298 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70298
  have eq70354 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq68149 eq70335
    | exact resolve eq70335 eq68149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70335
  have eq70393 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq70354 eq7413
    | exact resolve eq7413 eq70354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70354
  have eq70420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq70393
  have eq70432 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq70420
       have r₂ := eq27
       grind)
    | exact resolve eq70420 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70420
  have eq70810 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq70432 eq27
    | exact resolve eq27 eq70432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70432
  have eq73330 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33270 eq26
    | (have j1 := eq33270 (σ y)
       grind)
    | exact resolve eq26 eq33270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73584 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq73330 eq33270
    | exact resolve eq33270 eq73330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33270
  have eq73638 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq73330 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq73330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq73330
  have eq73639 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq73638
  have eq73656 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq73584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73584
  have eq73755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73639 eq4959
    | exact resolve eq4959 eq73639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4959
  have eq73760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73639 eq18305
    | exact resolve eq18305 eq73639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18305 eq73639
  have eq73800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq73760
  have eq73801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq73755
  have eq73840 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq73800
       have r₂ := eq27
       grind)
    | exact resolve eq73800 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73800
  have eq73844 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq73801
       have r₂ := eq27
       grind)
    | exact resolve eq73801 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73801
  have eq73899 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73844 eq13
    | (have j0 := eq13 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) x
       have r₂ := eq73844
       grind)
    | exact resolve eq13 eq73844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73900 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq73844 eq16
    | exact resolve eq16 eq73844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73906 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq73844 eq1373
    | exact resolve eq1373 eq73844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73921 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq73899 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73899
  have eq73956 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73840 eq13
    | (have j0 := eq13 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) x
       have r₂ := eq73840
       grind)
    | exact resolve eq13 eq73840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73957 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq73840 eq16
    | exact resolve eq16 eq73840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73963 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq73840 eq1373
    | exact resolve eq1373 eq73840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73978 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq73956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73956
  have eq73998 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq22680 eq73656
    | exact resolve eq73656 eq22680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22680 eq73656
  have eq74170 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq73998
  have eq74203 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq74170
       have r₂ := eq33254
       grind)
    | exact resolve eq74170 eq33254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33254 eq74170
  have eq74213 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq73840 eq74203
    | exact resolve eq74203 eq73840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74203
  have eq74214 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73840 eq74213
    | exact resolve eq74213 eq73840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74213
  have eq74215 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq74214
  have eq74216 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq10476 eq74215
    | exact resolve eq74215 eq10476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10476 eq74215
  have eq74217 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq34445 eq74216
    | exact resolve eq74216 eq34445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74216
  have eq74347 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73844 eq73900
    | exact resolve eq73900 eq73844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73844 eq73900
  have eq74488 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq74347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74347
  have eq75478 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73921 eq73906
    | exact resolve eq73906 eq73921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73906
  have eq75479 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73921 eq74488
    | exact resolve eq74488 eq73921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73921 eq74488
  have eq75549 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq75479
  have eq75550 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq75478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75478
  have eq75864 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60367 eq75549
    | exact resolve eq75549 eq60367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75549
  have eq75865 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq60367 eq75550
    | exact resolve eq75550 eq60367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60367 eq75550
  have eq76077 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq75864 eq75865
    | exact resolve eq75865 eq75864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75864 eq75865
  have eq76414 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76077 eq26
    | (have j1 := eq76077 (σ y)
       grind)
    | exact resolve eq26 eq76077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76077
  have eq76525 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq76414
  have eq77505 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq74217 eq7420
    | exact resolve eq7420 eq74217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7420 eq74217
  have eq77544 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq77505
  have eq77581 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq26634 eq77544
    | exact resolve eq77544 eq26634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26634 eq77544
  have eq77582 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq77581
  have eq77629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq34445 eq77582
    | exact resolve eq77582 eq34445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34445 eq77582
  have eq77630 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq77629
  have eq77674 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77630 eq40
    | exact resolve eq40 eq77630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq77630
  have eq77684 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq77674
    | exact resolve eq77674 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77674
  have eq77688 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76525 eq77684
    | exact resolve eq77684 eq76525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77684
  have eq77696 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77688 eq537
    | exact resolve eq537 eq77688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq77688
  have eq78351 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73840 eq73957
    | exact resolve eq73957 eq73840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73840 eq73957
  have eq78484 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq78351 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78351
  have eq78498 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76525 eq78484
    | exact resolve eq78484 eq76525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78484
  have eq78538 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq78498 eq77696
    | exact resolve eq77696 eq78498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77696 eq78498
  have eq78586 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq78538
  have eq78628 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq78586 eq27
    | exact resolve eq27 eq78586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78586
  have eq78689 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq78628
       have r₂ := eq76525
       grind)
    | exact resolve eq78628 eq76525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78628
  have eq78718 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq78689 eq12400
    | exact resolve eq12400 eq78689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12400
  have eq78735 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq78718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78718
  have eq78751 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1007 eq78735
    | (have j0 := eq78735 X0
       grind)
    | exact resolve eq78735 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq78735
  have eq78752 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq78751 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78751
  have eq79873 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73978 eq73963
    | exact resolve eq73963 eq73978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73963 eq73978
  have eq79956 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq79873 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79873
  have eq80184 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33249 eq79956
    | exact resolve eq79956 eq33249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79956
  have eq80308 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76525 eq80184
    | exact resolve eq80184 eq76525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76525 eq80184
  have eq80401 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq78689 eq80308
    | exact resolve eq80308 eq78689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80308
  have eq80657 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80401 eq26
    | (have j1 := eq80401 (σ y)
       grind)
    | exact resolve eq26 eq80401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80401
  have eq80763 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq80657
  have eq80799 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80763 eq27
    | exact resolve eq27 eq80763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81462 : ∀ X1 : G, x ≠ (M.op x y) ∨ (k x X1) = (M.op X1 x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq17432 x X1
       have i₂ := eq17371 x
       grind)
    | (have i₁ := eq17432 y X1
       have i₂ := eq17371 x
       grind)
    | exact superpose eq17371 eq17432
    | (have j0 := eq17432 y X1
       grind)
    | exact resolve eq17432 eq17371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17371 eq17432
  have eq81516 : ∀ X1 : G, x ≠ (M.op x y) ∨ (k x X1) = (M.op X1 x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have j0 := eq81462 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81462
  have eq81555 : ∀ X1 : G, (k x X1) = (M.op X1 x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have j0 := eq81516 X1
       grind)
    | (have r₁ := eq81516 X1
       have r₂ := eq80763
       grind)
    | exact resolve eq81516 eq80763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81516
  have eq81580 : ∀ X1 : G, (k (M.op x y) X1) = (M.op X1 (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq80763 eq81555
    | exact resolve eq81555 eq80763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81555
  have eq82056 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81580 eq31864
    | exact resolve eq31864 eq81580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31864
  have eq82179 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq82056
  have eq82393 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80763 eq82179
    | exact resolve eq82179 eq80763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80763 eq82179
  have eq82394 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq82393
  have eq82802 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq82394 eq42
    | exact resolve eq42 eq82394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82815 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq82394 eq551
    | (have j0 := eq551 (M.op x y)
       grind)
    | exact resolve eq551 eq82394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82394
  have eq82829 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq82815
  have eq82878 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq82829
    | exact resolve eq82829 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82829
  have eq82888 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq82802
    | exact resolve eq82802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82802
  have eq83145 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq82878 eq16
    | exact resolve eq16 eq82878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83156 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq82878 eq1393
    | exact resolve eq1393 eq82878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82878
  have eq83187 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq82888 eq83156
    | (have j0 := eq83156 X0
       grind)
    | exact resolve eq83156 eq82888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83156
  have eq83188 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq83187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83187
  have eq83246 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq82888 eq60457
    | exact resolve eq60457 eq82888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60457 eq82888
  have eq83271 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq83246
  have eq83478 : (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq83188 eq81580
    | exact resolve eq81580 eq83188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83188
  have eq83486 : (σ (M.op x y)) = (k (M.op x y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq83478
  have eq83514 : (σ x) = (k (M.op x y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq83271 eq83486
    | exact resolve eq83486 eq83271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83486
  have eq85164 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq81580 eq83145
    | exact resolve eq83145 eq81580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81580 eq83145
  have eq85279 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (M.op x y) (σ (M.op x y))) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq85164 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85164
  have eq85320 : ∀ X0 : G, (σ x) = (M.op (k (M.op x y) (σ x)) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq83271 eq85279
    | exact resolve eq85279 eq83271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83271 eq85279
  have eq85335 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq83514 eq85320
    | exact resolve eq85320 eq83514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83514 eq85320
  have eq85401 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85335 eq26
    | (have j1 := eq85335 (σ y)
       grind)
    | exact resolve eq26 eq85335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85335
  have eq85511 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq85401
  have eq85571 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85511 eq27
    | exact resolve eq27 eq85511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85585 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq85511 eq6014
    | exact resolve eq6014 eq85511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85609 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq85585 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85585
  have eq85633 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq78752 eq85609
    | (have j0 := eq85609 X0
       have j1 := eq78752 X0
       grind)
    | exact resolve eq85609 eq78752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78752 eq85609
  have eq85634 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq85633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85633
  have eq85732 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq85634 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq85634 (σ x)
       grind)
    | exact resolve eq13 eq85634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85783 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq85732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85732
  have eq87670 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5928 eq85783
    | exact resolve eq85783 eq5928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5928
  have eq88001 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85783 eq12630
    | exact resolve eq12630 eq85783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12630
  have eq88021 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85783 eq85634
    | exact resolve eq85634 eq85783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85783
  have eq88047 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq88021
  have eq88059 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq88001
  have eq88200 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq87670
  have eq88307 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq68149 eq88059
    | exact resolve eq88059 eq68149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88059
  have eq88431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5811 eq88200
    | exact resolve eq88200 eq5811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88200
  have eq88493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2054 eq88307
    | exact resolve eq88307 eq2054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054 eq88307
  have eq88549 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq88431
       have r₂ := eq27
       grind)
    | exact resolve eq88431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88431
  have eq88588 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq88493
       have r₂ := eq27
       grind)
    | exact resolve eq88493 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88493
  have eq88617 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq85511 eq88549
    | exact resolve eq88549 eq85511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88549
  have eq88618 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq88617
  have eq88631 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq78689 eq88588
    | exact resolve eq88588 eq78689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78689 eq88588
  have eq88632 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq88631
  have eq88655 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq88618 eq32
    | exact resolve eq32 eq88618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq88618
  have eq88847 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq88655
    | exact resolve eq88655 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88655
  have eq88848 : y = (M.op x y) ∨ x = y := by grind
  clear eq88847
  have eq88854 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq88848
       grind)
    | exact superpose eq88848 eq24
    | exact resolve eq24 eq88848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88924 : x ≠ (M.op x y) ∨ x = y := by grind
  have eq88956 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq88854
    | exact resolve eq88854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88854
  have eq89207 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq88956 eq33249
    | exact resolve eq33249 eq88956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33249
  have eq89246 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq88956 eq70810
    | (have r₁ := eq70810
       have r₂ := eq88956
       grind)
    | exact resolve eq70810 eq88956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70810
  have eq89262 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq89246
  have eq89263 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq89262
  have eq89277 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq89263
       have r₂ := eq88924
       grind)
    | exact resolve eq89263 eq88924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89263
  have eq89281 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq89207
       have r₂ := eq88924
       grind)
    | exact resolve eq89207 eq88924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89207
  have eq89304 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq85511 eq89277
    | exact resolve eq89277 eq85511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89277
  have eq89307 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85511 eq89281
    | exact resolve eq89281 eq85511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89281
  have eq89310 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq89304 eq89307
    | exact resolve eq89307 eq89304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89307
  have eq89654 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq89304 eq6014
    | exact resolve eq6014 eq89304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6014
  have eq89680 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq89654 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89654
  have eq89708 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq89680 X0
       grind)
    | (have r₁ := eq89680 X0
       have r₂ := eq88924
       grind)
    | exact resolve eq89680 eq88924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89680
  have eq89734 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq85634 eq89708
    | (have j0 := eq89708 X0
       have j1 := eq85634 X0
       grind)
    | exact resolve eq89708 eq85634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85634 eq89708
  have eq89781 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq88047 eq5811
    | exact resolve eq5811 eq88047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5811 eq88047
  have eq89834 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq89781
  have eq89864 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq89834
       have r₂ := eq85571
       grind)
    | exact resolve eq89834 eq85571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89834
  have eq89882 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq89864 eq26
    | exact resolve eq26 eq89864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89907 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq89864 eq544
    | exact resolve eq544 eq89864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq89929 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq89864 eq6801
    | exact resolve eq6801 eq89864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801
  have eq89963 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq89864 eq37380
    | exact resolve eq37380 eq89864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37380
  have eq89977 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq89963
  have eq90009 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq89977
       have r₂ := eq85571
       grind)
    | exact resolve eq89977 eq85571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89977
  have eq90016 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq89929
       have r₂ := eq85571
       grind)
    | exact resolve eq89929 eq85571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89929
  have eq90026 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq88848 eq89907
    | exact resolve eq89907 eq88848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88848 eq89907
  have eq90051 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85511 eq89882
    | exact resolve eq89882 eq85511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85511 eq89882
  have eq90057 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq90016 eq90026
    | exact resolve eq90026 eq90016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90016 eq90026
  have eq90059 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq90057
       have r₂ := eq85571
       grind)
    | exact resolve eq90057 eq85571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90057
  have eq90138 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq90051 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq90051
       grind)
    | exact resolve eq13 eq90051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90051
  have eq90160 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq90138 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90138
  have eq90263 : ∀ X0 : G, x ≠ x ∨ x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3661 X0
       have i₂ := eq90059
       grind)
    | exact superpose eq90059 eq3661
    | (have j0 := eq3661 X0
       grind)
    | (have r₁ := eq3661 X0
       have r₂ := eq90059
       grind)
    | exact resolve eq3661 eq90059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq90302 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14395 x
       have i₂ := eq90059
       grind)
    | exact superpose eq90059 eq14395
    | exact resolve eq14395 eq90059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14395 eq90059
  have eq90375 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq90302
  have eq90390 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq90263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90263
  have eq90434 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq88632 eq90375
    | exact resolve eq90375 eq88632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88632 eq90375
  have eq90447 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq88956 eq90390
    | (have j0 := eq90390 X0
       grind)
    | exact resolve eq90390 eq88956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90390
  have eq90480 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq90434
       have r₂ := eq80799
       grind)
    | exact resolve eq90434 eq80799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80799 eq90434
  have eq90490 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq90447 X0
       have j1 := eq3826 X0
       grind)
    | (have r₁ := eq90447 y
       have r₂ := eq3826 X0
       grind)
    | (have r₁ := eq90447 X0
       have r₂ := eq3826 X0
       grind)
    | exact resolve eq90447 eq3826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3826 eq90447
  have eq90539 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq90480
       grind)
    | exact superpose eq90480 eq24
    | exact resolve eq24 eq90480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90480
  have eq90634 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq90539
    | exact resolve eq90539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90539
  have eq91055 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28639 x
       have i₂ := eq90490 sF0
       grind)
    | exact superpose eq90490 eq28639
    | exact resolve eq28639 eq90490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28639 eq90490
  have eq91073 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y (M.op x y)) := by grind
  clear eq91055
  have eq91189 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq88956 eq91073
    | exact resolve eq91073 eq88956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88956 eq91073
  have eq91232 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq90634 eq91189
    | exact resolve eq91189 eq90634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91189
  have eq91254 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq90634 eq91232
    | exact resolve eq91232 eq90634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90634 eq91232
  have eq91255 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq91254
  have eq91679 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq91255 eq42
    | exact resolve eq42 eq91255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq91692 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq91255 eq551
    | (have j0 := eq551 (M.op x y)
       grind)
    | exact resolve eq551 eq91255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq91255
  have eq91706 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq91692
  have eq91767 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq91706
    | exact resolve eq91706 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91706
  have eq91771 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq91679
    | exact resolve eq91679 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91679
  have eq92006 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq91767 eq1393
    | exact resolve eq1393 eq91767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91767
  have eq92040 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq91771 eq92006
    | (have j0 := eq92006 X0
       grind)
    | exact resolve eq92006 eq91771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91771 eq92006
  have eq92041 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq92040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92040
  have eq94110 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq92041 eq90160
    | exact resolve eq90160 eq92041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90160 eq92041
  have eq94767 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq89864 eq94110
    | exact resolve eq94110 eq89864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89864 eq94110
  have eq94843 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq94767
       have r₂ := eq85571
       grind)
    | exact resolve eq94767 eq85571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94767
  have eq94883 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq90009 eq94843
    | exact resolve eq94843 eq90009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90009 eq94843
  have eq94908 : y = (M.op x y) := by
    first
    | (have r₁ := eq94883
       have r₂ := eq85571
       grind)
    | exact resolve eq94883 eq85571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85571 eq94883
  have eq95146 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq94908
       grind)
    | exact superpose eq94908 eq18
    | exact resolve eq18 eq94908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq95147 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq94908
       grind)
    | exact superpose eq94908 eq24
    | exact resolve eq24 eq94908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq95244 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq95147 eq20
    | exact resolve eq20 eq95147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103286 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq89310 eq7413
    | exact resolve eq7413 eq89310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7413 eq89310
  have eq103339 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq103286
  have eq103379 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq103339
       have r₂ := eq88924
       grind)
    | exact resolve eq103339 eq88924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88924 eq103339
  have eq103395 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103379
       have i₂ := eq94908
       grind)
    | exact superpose eq94908 eq103379
    | exact resolve eq103379 eq94908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94908 eq103379
  have eq103400 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq89304 eq103395
    | exact resolve eq103395 eq89304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89304 eq103395
  have eq103401 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq103400
  have eq103411 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103401 eq27
    | exact resolve eq27 eq103401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103489 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq95244 eq103411
    | exact resolve eq103411 eq95244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103411
  have eq103998 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq89734 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq89734 (σ x)
       grind)
    | exact resolve eq13 eq89734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104005 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq89734 eq1373
    | exact resolve eq1373 eq89734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373 eq89734
  have eq104055 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq103998 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103998
  have eq104112 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq104005 X0 X1
       grind)
    | (have r₁ := eq104005 X0 X1
       have r₂ := eq103489
       grind)
    | exact resolve eq104005 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104005
  have eq104118 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq104055 X0
       grind)
    | (have r₁ := eq104055 X0
       have r₂ := eq103489
       grind)
    | exact resolve eq104055 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104055
  have eq104495 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq104112 eq26
    | (have j1 := eq104112 (σ y) X0
       grind)
    | exact resolve eq26 eq104112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104112
  have eq104725 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq103401 eq104495
    | exact resolve eq104495 eq103401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104495
  have eq105827 : ∀ X0 : G, (M.op x X0) = (k (σ x) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq104118 eq67495
    | exact resolve eq67495 eq104118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67495
  have eq105829 : (M.op x y) = (k (σ x) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104118 eq68149
    | exact resolve eq68149 eq104118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68149
  have eq105885 : ∀ X0 : G, (M.op x y) = (k (σ x) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq104118 eq63187
    | (have j0 := eq63187 X0 X0
       grind)
    | exact resolve eq63187 eq104118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63187
  have eq105888 : x = (k (σ x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104118 eq67379
    | exact resolve eq67379 eq104118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67379
  have eq105995 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104118 eq104725
    | exact resolve eq104725 eq104118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104118 eq104725
  have eq106015 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq105995
  have eq106152 : x = (k (σ x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq105888
       have r₂ := eq103489
       grind)
    | exact resolve eq105888 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105888
  have eq106154 : ∀ X0 : G, (M.op x y) = (k (σ x) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq105885 X0
       grind)
    | (have r₁ := eq105885 X0
       have r₂ := eq103489
       grind)
    | exact resolve eq105885 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105885
  have eq106159 : (M.op x y) = (k (σ x) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq105829
       have r₂ := eq103489
       grind)
    | exact resolve eq105829 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105829
  have eq106161 : ∀ X0 : G, (M.op x X0) = (k (σ x) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq105827 X0
       grind)
    | (have r₁ := eq105827 X0
       have r₂ := eq103489
       grind)
    | exact resolve eq105827 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105827
  have eq106311 : x = (k (σ x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103401 eq106152
    | exact resolve eq106152 eq103401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106152
  have eq106313 : ∀ X0 : G, (M.op x y) = (k (σ x) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq103401 eq106154
    | (have j0 := eq106154 X0
       grind)
    | exact resolve eq106154 eq103401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106154
  have eq106318 : (M.op x y) = (k (σ x) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103401 eq106159
    | exact resolve eq106159 eq103401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106159
  have eq106320 : ∀ X0 : G, (M.op x X0) = (k (σ x) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq103401 eq106161
    | (have j0 := eq106161 X0
       grind)
    | exact resolve eq106161 eq103401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103401 eq106161
  have eq106424 : x = (k (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq106311
       have r₂ := eq103489
       grind)
    | exact resolve eq106311 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106311
  have eq106426 : ∀ X0 : G, (M.op x y) = (k (σ x) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq106313 X0
       grind)
    | (have r₁ := eq106313 X0
       have r₂ := eq103489
       grind)
    | exact resolve eq106313 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106313
  have eq106431 : (M.op x y) = (k (σ x) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq106318
       have r₂ := eq103489
       grind)
    | exact resolve eq106318 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106318
  have eq106433 : ∀ X0 : G, (M.op x X0) = (k (σ x) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq106320 X0
       grind)
    | (have r₁ := eq106320 X0
       have r₂ := eq103489
       grind)
    | exact resolve eq106320 eq103489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103489 eq106320
  have eq106510 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106424 eq106426
    | (have j0 := eq106426 X0
       grind)
    | exact resolve eq106426 eq106424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106424 eq106426
  have eq106511 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq106510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106510
  have eq106516 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106431 eq106433
    | exact resolve eq106433 eq106431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106431 eq106433
  have eq106815 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106511 eq1393
    | exact resolve eq1393 eq106511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393 eq106511
  have eq106943 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106516 eq106815
    | (have j0 := eq106815 y
       grind)
    | exact resolve eq106815 eq106516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106815
  have eq106983 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106516 eq106943
    | (have j0 := eq106943 y
       grind)
    | exact resolve eq106943 eq106516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106516 eq106943
  have eq106984 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq106983
  have eq107384 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106015 eq142
    | exact resolve eq142 eq106015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq106015
  have eq107436 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq107384
    | exact resolve eq107384 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq107384
  have eq107453 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106984 eq107436
    | exact resolve eq107436 eq106984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106984 eq107436
  have eq107454 : x = (M.op x y) := by grind
  clear eq107453
  have eq107471 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq107454
       grind)
    | exact superpose eq107454 eq22
    | exact resolve eq22 eq107454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq107683 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq95146
       have i₂ := eq107454
       grind)
    | exact superpose eq107454 eq95146
    | exact resolve eq95146 eq107454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95146 eq107454
  have eq107745 : (σ x) = (σ y) := by
    first
    | exact superpose eq107471 eq95147
    | exact resolve eq95147 eq107471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95147
  have eq107746 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq107471 eq20
    | exact resolve eq20 eq107471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107471
  have eq107963 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq107745 eq26
    | exact resolve eq26 eq107745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq108623 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq107683 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq107683
       grind)
    | exact resolve eq13 eq107683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108624 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq107683 eq16
    | exact resolve eq16 eq107683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108645 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq108623 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108623
  have eq109248 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq107683 eq108624
    | exact resolve eq108624 eq107683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107683 eq108624
  have eq110736 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq108645 eq109248
    | exact resolve eq109248 eq108645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108645 eq109248
  have eq111092 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq110736 eq38
    | exact resolve eq38 eq110736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq111110 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq110736 eq727
    | (have j0 := eq727 (M.op x y) X0
       grind)
    | exact resolve eq727 eq110736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq110736
  have eq111120 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq111110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111110
  have eq111147 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq111120
    | (have j0 := eq111120 X0
       grind)
    | exact resolve eq111120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111120
  have eq111151 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq111092
    | exact resolve eq111092 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq111092
  have eq111156 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq95244 eq111147
    | exact resolve eq111147 eq95244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111147
  have eq111160 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq95244 eq111151
    | exact resolve eq111151 eq95244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95244 eq111151
  have eq111165 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq107745 eq111156
    | exact resolve eq111156 eq107745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111156
  have eq111169 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq107745 eq111160
    | exact resolve eq111160 eq107745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107745 eq111160
  have eq112498 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq111165 eq107963
    | exact resolve eq107963 eq111165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107963 eq111165
  have eq112577 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq111169 eq112498
    | exact resolve eq112498 eq111169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111169 eq112498
  have eq112754 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq112577 eq27
    | exact resolve eq27 eq112577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq112577
  have eq112813 : False := by grind
  exact eq112813

/-- `Equation4076`: `x ◇ x = ((x ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation4076 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4076 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4076.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq38 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq135 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq35 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq35 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq35 X1 X1
       grind)
    | exact resolve eq13 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq35 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq35 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq35 X0 X1
       grind)
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq146 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq137 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq137 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq137 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq147 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq135 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq135 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | exact resolve eq135 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq150 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq146
    | (have j0 := eq146 X0 X1
       grind)
    | exact resolve eq146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq147
    | (have j0 := eq147 X0 X1
       grind)
    | exact resolve eq147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq152 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq315 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = X1 ∨ (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq38 X0 X1
       grind)
    | (have r₁ := eq12 X1 (τ X0)
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq38 X0 (τ X0)
       grind)
    | exact resolve eq12 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (τ X0) ≠ X1 ∨ (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq322 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq684 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (τ X1) (τ X0)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq150
    | (have j0 := eq150 (τ X0) (τ X1)
       grind)
    | exact resolve eq150 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq684
    | (have j0 := eq684 X0 X1
       grind)
    | exact resolve eq684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq707 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq700 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq700
    | (have j0 := eq700 X0 X1
       grind)
    | exact resolve eq700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq712 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq707
    | (have j0 := eq707 X0 X1
       grind)
    | exact resolve eq707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq717 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq712 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq712
    | (have j0 := eq712 X0 X1
       grind)
    | exact resolve eq712 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq722 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq717 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq717
    | (have j0 := eq717 X0 X1
       grind)
    | exact resolve eq717 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq727 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq722
    | (have j0 := eq722 X0 X1
       grind)
    | exact resolve eq722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq744 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq152 (τ X1) (τ X0)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq152
    | (have j0 := eq152 (τ X0) (τ X1)
       grind)
    | exact resolve eq152 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq744 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq744
    | (have j0 := eq744 X0 X1
       grind)
    | exact resolve eq744 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq767 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq760 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq760
    | (have j0 := eq760 X0 X1
       grind)
    | exact resolve eq760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq772 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq767 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq767
    | (have j0 := eq767 X0 X1
       grind)
    | exact resolve eq767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq777 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq772
    | (have j0 := eq772 X0 X1
       grind)
    | exact resolve eq772 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq782 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq777
    | (have j0 := eq777 X0 X1
       grind)
    | exact resolve eq777 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq787 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq782
    | (have j0 := eq782 X0 X1
       grind)
    | exact resolve eq782 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq3565 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq320 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq3566 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3565 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3565
    | (have j0 := eq3565 X0
       grind)
    | exact resolve eq3565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565
  have eq3996 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq3566 X0
       grind)
    | exact superpose eq3566 eq10
    | (have j1 := eq3566 X0
       grind)
    | exact resolve eq10 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq4404 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq3996 X0
       grind)
    | exact superpose eq3996 eq12
    | (have j0 := eq12 (τ X0) (τ X0)
       have j1 := eq3996 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq3996 X0
       grind)
    | exact resolve eq12 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4446 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3996 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3996
  have eq4448 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4404 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4404
  have eq4449 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4448 X0
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq4448
    | (have j0 := eq4448 X0
       grind)
    | exact resolve eq4448 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4448
  have eq5965 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4449 X0
       have j1 := eq4446 X0
       grind)
    | (have r₁ := eq4449 X0
       have r₂ := eq4446 X0
       grind)
    | exact resolve eq4449 eq4446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4446 eq4449
  have eq6217 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5965 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5965
    | exact resolve eq5965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5965
  have eq6291 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq6217 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq6217
    | exact resolve eq6217 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6217
  have eq6293 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6291 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6291
    | exact resolve eq6291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6291
  have eq6324 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6293 (σ X0)
       grind)
    | exact superpose eq6293 eq15
    | exact resolve eq15 eq6293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6364 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6324 X0
       have i₂ := eq6293 X0
       grind)
    | exact superpose eq6293 eq6324
    | exact resolve eq6324 eq6293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6293 eq6324
  have eq17037 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq322 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq322
    | exact resolve eq322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17046 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op (τ X1) X0) = X0 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq322 X1 X0
       grind)
    | exact superpose eq322 eq18
    | (have j1 := eq322 X1 X0
       grind)
    | exact resolve eq18 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq322
  have eq17130 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17037 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17037
    | (have j0 := eq17037 X0 X1
       grind)
    | exact resolve eq17037 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17037
  have eq17565 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq17130 X0 X1
       grind)
    | exact superpose eq17130 eq10
    | (have j1 := eq17130 X0 X1
       grind)
    | exact resolve eq10 eq17130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17130
  have eq17626 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17565 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq17565
    | (have j0 := eq17565 X0 X1
       grind)
    | exact resolve eq17565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17565
  have eq17720 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq17626 (σ X0) X1
       grind)
    | exact superpose eq17626 eq25
    | (have j1 := eq17626 (σ X0) X1
       grind)
    | exact resolve eq25 eq17626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17626
  have eq29538 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X1)
       have i₂ := eq17720 X1 (σ X0)
       grind)
    | exact superpose eq17720 eq32
    | (have j1 := eq17720 X1 (σ X0)
       grind)
    | exact resolve eq32 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17720
  have eq29622 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29538 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq29538
    | (have j0 := eq29538 X0 X1
       grind)
    | exact resolve eq29538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29538
  have eq29660 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29622 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29622
    | (have j0 := eq29622 X0 X1
       grind)
    | exact resolve eq29622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29622
  have eq29681 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29660 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29660
    | (have j0 := eq29660 X0 X1
       grind)
    | exact resolve eq29660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29660
  have eq35264 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op (τ X1) X0) = X0 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq17046 X0 X1
       grind)
    | exact superpose eq17046 eq10
    | (have j1 := eq17046 X0 X1
       grind)
    | exact resolve eq10 eq17046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17046
  have eq35365 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op (τ X1) X0) = X0 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35264 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq35264
    | (have j0 := eq35264 X0 X1
       grind)
    | exact resolve eq35264 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq35264
  have eq36885 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op (τ X0) X1) = X1 ∨ (M.op (τ X0) X1) = X1 ∨ (σ X1) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 (τ X1)
       have i₂ := eq35365 X0 X1
       grind)
    | exact superpose eq35365 eq727
    | (have j0 := eq727 (σ X1) X0
       have j1 := eq35365 X1 X0
       grind)
    | (have r₁ := eq727 (σ X0) (σ X0)
       have r₂ := eq35365 X0 (σ X0)
       grind)
    | exact resolve eq727 eq35365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35365
  have eq36947 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 ∨ (σ X1) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq36885 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36885
  have eq37212 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (σ X1) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36947 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36947
    | (have j0 := eq36947 (σ X0) X1
       grind)
    | exact resolve eq36947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36947
  have eq37238 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (σ X1) = (σ (k X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37212 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq37212
    | (have j0 := eq37212 X0 X1
       grind)
    | exact resolve eq37212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37212
  have eq67837 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq29681 X0 X1
       grind)
    | exact superpose eq29681 eq11
    | (have j1 := eq29681 X0 X1
       grind)
    | exact resolve eq11 eq29681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29681
  have eq83831 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67837 y x
       grind)
    | exact superpose eq67837 eq16
    | (have j1 := eq67837 y x
       grind)
    | exact resolve eq16 eq67837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84004 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (k X1 X0) = X1 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67837 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67837
  have eq85425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83831
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq83831
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq83831 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83831
  have eq85438 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85425
  have eq85439 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85438
  have eq85687 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq85439
       grind)
    | exact superpose eq85439 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq85439
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq85439
       grind)
    | exact resolve eq13 eq85439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85745 : x ≠ y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85439
  have eq85746 : x = y ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85687
  have eq90302 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq85746
       have r₂ := eq85745
       grind)
    | exact resolve eq85746 eq85745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85746
  have eq90313 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq150 y x
       have i₂ := eq90302
       grind)
    | exact superpose eq90302 eq150
    | (have j0 := eq150 y x
       grind)
    | exact resolve eq150 eq90302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq90370 : (σ x) ≠ (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84004 x y
       have i₂ := eq90302
       grind)
    | exact superpose eq90302 eq84004
    | (have j0 := eq84004 x y
       grind)
    | exact resolve eq84004 eq90302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84004 eq90302
  have eq90372 : (σ x) ≠ (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq90370
  have eq90409 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq90313
  have eq90410 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq90409
  have eq90422 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq90372
       have r₂ := eq85745
       grind)
    | exact resolve eq90372 eq85745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85745 eq90372
  have eq90522 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq90422
       have r₂ := eq90410
       grind)
    | exact resolve eq90422 eq90410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90410 eq90422
  have eq90532 : x ≠ x ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq90522
       grind)
    | exact superpose eq90522 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq90522
       grind)
    | exact resolve eq12 eq90522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90589 : x ≠ x ∨ (σ y) = (σ (k y x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37238 x y
       have i₂ := eq90522
       grind)
    | exact superpose eq90522 eq37238
    | (have j0 := eq37238 x y
       grind)
    | (have r₁ := eq37238 x y
       have r₂ := eq90522
       grind)
    | exact resolve eq37238 eq90522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37238 eq90522
  have eq90596 : x = y ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq90589
  have eq90598 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq90532
  have eq90624 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq141 x y
       have i₂ := eq90598
       grind)
    | exact superpose eq90598 eq141
    | (have j0 := eq141 x y
       grind)
    | exact resolve eq141 eq90598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq90598
  have eq90666 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq90624
  have eq90667 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq90666
  have eq91004 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq90667
       grind)
    | exact superpose eq90667 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq90667
       grind)
    | exact resolve eq12 eq90667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91063 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq90667
  have eq91121 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq91004
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq91004 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91004
  have eq91157 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq91121
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq91121
    | exact resolve eq91121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91121
  have eq93235 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq90596
       grind)
    | exact superpose eq90596 eq16
    | exact resolve eq16 eq90596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90596
  have eq93285 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq93235
       have r₂ := eq6364 x
       grind)
    | exact resolve eq93235 eq6364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93235
  have eq93304 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq93285
       grind)
    | exact superpose eq93285 eq16
    | exact resolve eq16 eq93285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93310 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq93285
       grind)
    | exact superpose eq93285 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq93285
       grind)
    | exact resolve eq13 eq93285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93285
  have eq93368 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq93310
  have eq93426 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq93368
       have r₂ := eq91157
       grind)
    | exact resolve eq93368 eq91157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91157 eq93368
  have eq93467 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq93426
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq93426
    | exact resolve eq93426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93426
  have eq93976 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq152 y x
       have i₂ := eq93467
       grind)
    | exact superpose eq93467 eq152
    | (have j0 := eq152 y x
       grind)
    | (have r₁ := eq152 y x
       have r₂ := eq93467
       grind)
    | exact resolve eq152 eq93467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq93990 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq93467
       grind)
    | exact superpose eq93467 eq10
    | exact resolve eq10 eq93467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93467
  have eq94129 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq93976
  have eq94162 : y = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq93990
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq93990
    | exact resolve eq93990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93990
  have eq94168 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq94129
       have r₂ := eq91063
       grind)
    | exact resolve eq94129 eq91063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91063 eq94129
  have eq94650 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq787 y x
       have i₂ := eq94162
       grind)
    | exact superpose eq94162 eq787
    | (have j0 := eq787 y x
       grind)
    | (have r₁ := eq787 y x
       have r₂ := eq94162
       grind)
    | exact resolve eq787 eq94162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq94162
  have eq94677 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq94650
  have eq95436 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94168
       grind)
    | exact superpose eq94168 eq16
    | exact resolve eq16 eq94168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94168
  have eq96917 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94677
       grind)
    | exact superpose eq94677 eq16
    | exact resolve eq16 eq94677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94677
  have eq96984 : x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq96917
       have r₂ := eq6364 x
       grind)
    | exact resolve eq96917 eq6364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96917
  have eq97013 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq95436
       have i₂ := eq96984
       grind)
    | exact superpose eq96984 eq95436
    | exact resolve eq95436 eq96984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95436 eq96984
  have eq97082 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq97013
  have eq97083 : (σ x) = (σ (k y x)) := by grind
  clear eq97082
  have eq97602 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq97083
       grind)
    | exact superpose eq97083 eq10
    | exact resolve eq10 eq97083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97777 : x = (k y x) := by
    first
    | (have i₁ := eq97602
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq97602
    | exact resolve eq97602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97602
  have eq97809 : x ≠ x ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq727 y x
       have i₂ := eq97777
       grind)
    | exact superpose eq97777 eq727
    | (have j0 := eq727 y x
       grind)
    | (have r₁ := eq727 y x
       have r₂ := eq97777
       grind)
    | exact resolve eq727 eq97777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq97777
  have eq97865 : x = y ∨ y = (M.op x y) := by grind
  clear eq97809
  have eq98397 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97865
       grind)
    | exact superpose eq97865 eq16
    | exact resolve eq16 eq97865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97865
  have eq98470 : y = (M.op x y) := by
    first
    | (have r₁ := eq98397
       have r₂ := eq6364 x
       grind)
    | exact resolve eq98397 eq6364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98397
  have eq98500 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq93304
       have i₂ := eq98470
       grind)
    | exact superpose eq98470 eq93304
    | exact resolve eq93304 eq98470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93304 eq98470
  have eq98564 : (σ y) = (σ (k y x)) := by grind
  clear eq98500
  have eq98572 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq98564
       have i₂ := eq97083
       grind)
    | exact superpose eq97083 eq98564
    | exact resolve eq98564 eq97083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97083 eq98564
  have eq99227 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq98572
       grind)
    | exact superpose eq98572 eq10
    | exact resolve eq10 eq98572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98572
  have eq99407 : x = y := by
    first
    | (have i₁ := eq99227
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq99227
    | exact resolve eq99227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99227
  have eq99421 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99407
       grind)
    | exact superpose eq99407 eq16
    | exact resolve eq16 eq99407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99407
  have eq99495 : False := by grind
  exact eq99495

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_x_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ X0 ∨ (k X0 X4) = (M.op X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X0 X4
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X4
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq79 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq98
    | (have j0 := eq98 (σ X0) (σ X1)
       grind)
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq98 x x
       grind)
    | exact superpose eq98 eq44
    | (have j1 := eq98 x x
       grind)
    | exact resolve eq44 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq98 y x
       grind)
    | exact superpose eq98 eq78
    | (have j1 := eq98 y x
       grind)
    | exact resolve eq78 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq98 y y
       grind)
    | exact superpose eq98 eq79
    | (have j1 := eq98 y y
       grind)
    | exact resolve eq79 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq109
    | exact resolve eq109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq121
    | exact resolve eq121 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq130 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq166 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq98 (τ X1) X0
       grind)
    | exact superpose eq98 eq35
    | (have j1 := eq98 (τ X1) X0
       grind)
    | exact resolve eq35 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq98 X1 (τ X0)
       grind)
    | exact superpose eq98 eq39
    | (have j1 := eq98 X1 (τ X0)
       grind)
    | exact resolve eq39 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X0 x X1
       have i₂ := eq57 X0 x X2
       grind)
    | (have i₁ := eq57 X0 X0 x
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq57 X0 X1 X5
       have i₂ := eq14 (M.op X0 X1) X2 X3 X4
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq122 eq98
    | (have j0 := eq98 (σ y) (σ x)
       grind)
    | exact resolve eq98 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq887
    | exact resolve eq887 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq891 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq888
       have r₂ := eq28
       grind)
    | exact resolve eq888 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq894 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  have eq899 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq891 eq57
    | exact resolve eq57 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq899
    | (have j0 := eq899 (σ y)
       grind)
    | exact resolve eq899 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq920 eq899
    | exact resolve eq899 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq920
  have eq950 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq1129 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ X0) X1) X2) X3) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (M.op (M.op (σ X0) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq102 X1 X1
       have i₂ := eq14 (σ X1) X1 X2 X3
       grind)
    | exact superpose eq14 eq102
    | exact resolve eq102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1132 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq1133 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq102 X0 X0
       grind)
    | exact superpose eq102 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq102 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq102 X1 X1
       grind)
    | exact resolve eq13 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1141 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq102 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1142 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1133 X0 X1
       have j1 := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq1133 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | exact resolve eq1133 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1143 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1132 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq1132
    | (have j0 := eq1132 X0
       grind)
    | exact resolve eq1132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1583 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq894 eq122
    | exact resolve eq122 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1586 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq1583
  have eq1692 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y y x x
       have i₂ := eq1586
       grind)
    | exact superpose eq1586 eq14
    | exact resolve eq14 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1695 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 y y X2 X3 x x
       have i₂ := eq1586
       grind)
    | exact superpose eq1586 eq52
    | exact resolve eq52 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1697 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq57 y y x
       have i₂ := eq1586
       grind)
    | exact superpose eq1586 eq57
    | exact resolve eq57 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1702 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X3
    first
    | (have i₁ := eq1695 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq1695
    | exact resolve eq1695 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1706 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1702 x
       have i₂ := eq208 x
       grind)
    | exact superpose eq208 eq1702
    | exact resolve eq1702 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq1702
  have eq1940 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq410 y X1 x
       have i₂ := eq1586
       grind)
    | exact superpose eq1586 eq410
    | exact resolve eq410 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq2107 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1692 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1692
    | (have j0 := eq1692 y X0
       grind)
    | exact resolve eq1692 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq2193 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1697 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1697
    | (have j0 := eq1697 y
       grind)
    | exact resolve eq1697 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2229 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1697 X0
       have i₂ := eq2193
       grind)
    | exact superpose eq2193 eq1697
    | exact resolve eq1697 eq2193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697 eq2193
  have eq2248 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229
  have eq7173 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq335
    | exact resolve eq335 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq7210 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq40 eq7173
    | (have j0 := eq7173 X0
       grind)
    | exact resolve eq7173 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq7173
  have eq7220 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k (σ (τ X0)) X1) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1142 (τ X0) X1
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1142
    | (have j0 := eq1142 (τ X0) X1
       grind)
    | exact resolve eq1142 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1142
  have eq7227 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k (σ (τ X0)) X1) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7220 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7220
    | (have j0 := eq7220 X0 X1
       grind)
    | exact resolve eq7220 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7220
  have eq7232 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7227 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7227
    | (have j0 := eq7227 X0 X1
       grind)
    | exact resolve eq7227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7227
  have eq7287 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op (τ X0) (τ X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq307 x X0
       have i₂ := eq2248 (τ X0)
       grind)
    | exact superpose eq2248 eq307
    | (have j0 := eq307 x X0
       grind)
    | exact resolve eq307 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7291 : ∀ X0 : G, (σ x) = (k X0 (σ (M.op x y))) ∨ (M.op x y) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2107 eq307
    | (have j0 := eq307 (M.op x y) X0
       grind)
    | exact resolve eq307 eq2107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq2107
  have eq7356 : ∀ X0 : G, (σ x) = (k X0 (σ (M.op x y))) ∨ (M.op x y) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21 eq7291
    | (have j0 := eq7291 X0
       grind)
    | exact resolve eq7291 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7291
  have eq7360 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op (τ X0) (τ X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7287 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq7287
    | (have j0 := eq7287 X0
       grind)
    | exact resolve eq7287 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7287
  have eq7380 : ∀ X0 : G, (M.op x y) = (M.op (τ X0) (τ X0)) ∨ (σ x) = (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7356 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq7356
    | (have j0 := eq7356 X0
       grind)
    | exact resolve eq7356 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356
  have eq7382 : ∀ X0 : G, x = (M.op (τ X0) (τ X0)) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21 eq7360
    | (have j0 := eq7360 X0
       grind)
    | exact resolve eq7360 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7360
  have eq16290 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq7380
    | (have j0 := eq7380 (σ (M.op x y))
       grind)
    | exact resolve eq7380 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7380
  have eq16353 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16290 eq166
    | exact resolve eq166 eq16290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq16290
  have eq16358 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq16353
    | exact resolve eq16353 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16353
  have eq16395 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq16358 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq16358
       grind)
    | exact resolve eq13 eq16358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16358
  have eq16421 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq16395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16395
  have eq18743 : ∀ X0 X1 X2 : G, (σ (k x x)) = (M.op (M.op (M.op (σ x) X0) X1) X2) ∨ (σ x) = (M.op (M.op (M.op (σ x) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1129 x X0 X1 X2
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1129
    | (have j0 := eq1129 x X0 X1 X2
       grind)
    | exact resolve eq1129 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18744 : ∀ X0 X1 X2 : G, (σ (k y y)) = (M.op (M.op (M.op (σ y) X0) X1) X2) ∨ (σ y) = (M.op (M.op (M.op (σ y) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1129 y X0 X1 X2
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1129
    | (have j0 := eq1129 y X0 X1 X2
       grind)
    | exact resolve eq1129 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18745 : ∀ X0 X1 X2 : G, (σ (k (M.op x y) (M.op x y))) = (M.op (M.op (M.op (σ (M.op x y)) X0) X1) X2) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq21 eq1129
    | (have j0 := eq1129 (M.op x y) X0 X1 X2
       grind)
    | exact resolve eq1129 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq18959 : ∀ X0 X1 X2 : G, (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18745 X1 X2 x
       have i₂ := eq14 sF1 X1 X2 x
       grind)
    | exact superpose eq14 eq18745
    | (have j0 := eq18745 X0 X1 X2
       grind)
    | exact resolve eq18745 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18745
  have eq18960 : ∀ X0 X1 X2 : G, (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (M.op (σ y) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18744 X1 X2 x
       have i₂ := eq14 sF3 X1 X2 x
       grind)
    | exact superpose eq14 eq18744
    | (have j0 := eq18744 X0 X1 X2
       grind)
    | exact resolve eq18744 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18744
  have eq18961 : ∀ X0 X1 X2 : G, (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ x) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18743 X1 X2 x
       have i₂ := eq14 sF2 X1 X2 x
       grind)
    | exact superpose eq14 eq18743
    | (have j0 := eq18743 X0 X1 X2
       grind)
    | exact resolve eq18743 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18743
  have eq19012 : ∀ X0 X1 X2 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq132 eq18959
    | (have j0 := eq18959 X0 X1 X2
       grind)
    | exact resolve eq18959 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18959
  have eq19013 : ∀ X0 X1 X2 : G, (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (M.op (σ y) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18960 X0 X1 X2
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq18960
    | (have j0 := eq18960 X0 X1 X2
       grind)
    | exact resolve eq18960 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq18960
  have eq19014 : ∀ X0 X1 X2 : G, (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (M.op (σ x) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18961 X0 X1 X2
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq18961
    | (have j0 := eq18961 X0 X1 X2
       grind)
    | exact resolve eq18961 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18961
  have eq19039 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq70 (σ (M.op x y)) x x x (σ (M.op x y))
       grind)
    | (have r₁ := eq19012 x x x
       have r₂ := eq70 (σ (M.op x y)) x x x x
       grind)
    | exact resolve eq19012 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19012
  have eq19040 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq70 (σ y) x x x (σ y)
       grind)
    | (have r₁ := eq19013 x x x
       have r₂ := eq70 (σ y) x x x x
       grind)
    | exact resolve eq19013 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19013
  have eq19041 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq70 (σ x) x x x (σ x)
       grind)
    | (have r₁ := eq19014 x x x
       have r₂ := eq70 (σ x) x x x x
       grind)
    | exact resolve eq19014 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq19014
  have eq19498 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1143 X0
       have j1 := eq1141 X0
       grind)
    | (have r₁ := eq1143 X0
       have r₂ := eq1141 X0
       grind)
    | exact resolve eq1143 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq21701 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq7382
    | (have j0 := eq7382 (σ x)
       grind)
    | exact resolve eq7382 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7382
  have eq29685 : x ≠ (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq16421
  have eq29711 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq29685
       have r₂ := eq1706
       grind)
    | exact resolve eq29685 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706 eq29685
  have eq29745 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29711 eq132
    | exact resolve eq132 eq29711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq29748 : (σ (M.op x y)) = (σ (k (M.op x y) x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29711 eq19498
    | (have j0 := eq19498 (M.op x y)
       grind)
    | exact resolve eq19498 eq29711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19498
  have eq29751 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29711 eq1141
    | (have j0 := eq1141 (M.op x y)
       grind)
    | exact resolve eq1141 eq29711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq29768 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq29751
    | exact resolve eq29751 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29751
  have eq29771 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq130 eq29748
    | exact resolve eq29748 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29748
  have eq29772 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29745
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29745
    | exact resolve eq29745 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29745
  have eq29779 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29768
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29768
    | exact resolve eq29768 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29768
  have eq29782 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq29771
    | exact resolve eq29771 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29771
  have eq29789 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq29779
    | exact resolve eq29779 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29779
  have eq29792 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq29782
    | exact resolve eq29782 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29782
  have eq51260 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29772 eq19039
    | exact resolve eq19039 eq29772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19039 eq29772
  have eq51298 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq51260 eq410
    | exact resolve eq410 eq51260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51299 : ∀ X0 X1 X2 X3 X4 : G, (M.op (σ x) X4) = (M.op (M.op (M.op (M.op (σ (M.op x y)) X0) X1) X2) X3) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq51260 eq417
    | exact resolve eq417 eq51260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq51260
  have eq51377 : ∀ X3 X4 : G, (M.op (σ x) X4) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X3) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X3 X4
    first
    | (have i₁ := eq51299 x x X3 X3 X4
       have i₂ := eq14 sF1 x x X3
       grind)
    | exact superpose eq14 eq51299
    | exact resolve eq51299 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51299
  have eq51822 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21701 eq19041
    | exact resolve eq19041 eq21701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21701
  have eq51860 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq27 eq51298
    | (have j0 := eq51298 (σ y) X0
       grind)
    | exact resolve eq51298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51298
  have eq56442 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq51377 eq51860
    | (have j1 := eq51377 X0 (σ y)
       grind)
    | exact resolve eq51860 eq51377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51377
  have eq56594 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq56442 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56442
  have eq56872 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56594 x
       have i₂ := eq57 sF1 x x
       grind)
    | (have i₁ := eq56594 (M.op sF1 sF1)
       have i₂ := eq57 sF1 sF1 x
       grind)
    | exact superpose eq57 eq56594
    | exact resolve eq56594 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq56594
  have eq62062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq51822 eq51860
    | exact resolve eq51860 eq51822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51822 eq51860
  have eq62118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq62062
  have eq62167 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq62118
       have r₂ := eq28
       grind)
    | exact resolve eq62118 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62118
  have eq62343 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1940 X0 x
       have i₂ := eq62167
       grind)
    | exact superpose eq62167 eq1940
    | exact resolve eq1940 eq62167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq62346 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2248 x
       have i₂ := eq62167
       grind)
    | exact superpose eq62167 eq2248
    | exact resolve eq2248 eq62167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248 eq62167
  have eq62430 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq62346
  have eq62433 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq62343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62343
  have eq68375 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq29711 eq7232
    | (have j0 := eq7232 (M.op x y) X0
       grind)
    | exact resolve eq7232 eq29711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29711
  have eq68397 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq68375 X0
       grind)
    | (have r₁ := eq68375 X0
       have r₂ := eq62430
       grind)
    | exact resolve eq68375 eq62430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62430 eq68375
  have eq68472 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq68397 eq130
    | exact resolve eq130 eq68397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq68397
  have eq74364 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68472
       have i₂ := eq62433 sF0
       grind)
    | exact superpose eq62433 eq68472
    | exact resolve eq68472 eq62433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62433 eq68472
  have eq74438 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq74364
  have eq74451 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74438
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq74438
    | exact resolve eq74438 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74438
  have eq74733 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq74451 eq29792
    | exact resolve eq29792 eq74451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29792 eq74451
  have eq74754 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq74733
  have eq74768 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq74754
       have r₂ := eq29789
       grind)
    | exact resolve eq74754 eq29789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29789 eq74754
  have eq75572 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq74768 eq56872
    | exact resolve eq56872 eq74768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56872
  have eq75626 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq75572
  have eq76005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq75626 eq74768
    | exact resolve eq74768 eq75626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74768 eq75626
  have eq76063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq76005
  have eq76118 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq76063
       have r₂ := eq28
       grind)
    | exact resolve eq76063 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76063
  have eq76165 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq76118 eq27
    | exact resolve eq27 eq76118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76166 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq76118 eq30
    | exact resolve eq30 eq76118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76174 : (τ (k (σ x) (σ x))) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq76118 eq87
    | exact resolve eq87 eq76118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76118
  have eq76219 : (k x x) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq50 eq76174
    | exact resolve eq76174 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq76174
  have eq76227 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq76166
    | exact resolve eq76166 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76166
  have eq77148 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19041 eq108
    | exact resolve eq108 eq19041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq77523 : (σ (k x x)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq76219
       grind)
    | exact superpose eq76219 eq78
    | exact resolve eq78 eq76219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76219
  have eq77568 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq77523
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq77523
    | exact resolve eq77523 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77523
  have eq77579 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19041 eq77568
    | exact resolve eq77568 eq19041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77568
  have eq77707 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19040 eq111
    | exact resolve eq111 eq19040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq19040
  have eq79660 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq77579 eq87
    | exact resolve eq87 eq77579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq77579
  have eq81617 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq76165 eq79660
    | exact resolve eq79660 eq76165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76165 eq79660
  have eq81682 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq81617
  have eq81699 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq81682
       grind)
    | exact superpose eq81682 eq78
    | exact resolve eq78 eq81682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq81750 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq81699
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq81699
    | exact resolve eq81699 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81699
  have eq81794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq81750 eq122
    | exact resolve eq122 eq81750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq81750
  have eq81824 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq81794
       have r₂ := eq28
       grind)
    | exact resolve eq81794 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81794
  have eq81865 : ∀ X0 : G, x ≠ y ∨ (k y X0) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq81824
       grind)
    | exact superpose eq81824 eq13
    | (have j0 := eq13 y X0
       grind)
    | exact resolve eq13 eq81824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81824
  have eq81965 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq81865 X0
       grind)
    | (have r₁ := eq81865 X0
       have r₂ := eq76227
       grind)
    | exact resolve eq81865 eq76227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76227 eq81865
  have eq83732 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq81682
       have i₂ := eq81965 x
       grind)
    | exact superpose eq81965 eq81682
    | exact resolve eq81682 eq81965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81682 eq81965
  have eq83780 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq83732
  have eq83799 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq83780
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83780
    | exact resolve eq83780 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83780
  have eq83858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq83799 eq15
    | exact resolve eq15 eq83799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83799
  have eq83900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq83858
    | exact resolve eq83858 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq83858
  have eq83903 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq83900
       have r₂ := eq28
       grind)
    | exact resolve eq83900 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83900
  have eq83907 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq83903 eq27
    | exact resolve eq27 eq83903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq83908 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq83903 eq30
    | exact resolve eq30 eq83903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq83927 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq83903 eq891
    | exact resolve eq891 eq83903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq83976 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq83908
    | exact resolve eq83908 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83908
  have eq83980 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op y X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq83976 eq55
    | exact resolve eq55 eq83976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq89131 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq83903 eq77707
    | exact resolve eq77707 eq83903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77707
  have eq89690 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq89131
       grind)
    | exact superpose eq89131 eq16
    | exact resolve eq16 eq89131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90302 : (τ (σ x)) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq83927 eq89690
    | exact resolve eq89690 eq83927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83927 eq89690
  have eq90375 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq90302
    | exact resolve eq90302 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq90302
  have eq90376 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq90375
  have eq90462 : ∀ X0 X1 : G, y = (M.op (M.op y X0) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y y x x
       have i₂ := eq90376
       grind)
    | exact superpose eq90376 eq14
    | exact resolve eq14 eq90376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90503 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq90376
  have eq90542 : y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90462 x x
       have i₂ := eq83980 x x
       grind)
    | exact superpose eq83980 eq90462
    | exact resolve eq90462 eq83980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90462
  have eq90629 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq77148
       have i₂ := eq90542
       grind)
    | exact superpose eq90542 eq77148
    | exact resolve eq77148 eq90542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90542
  have eq90769 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq90629
       have r₂ := eq90503
       grind)
    | exact resolve eq90629 eq90503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90503 eq90629
  have eq90804 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90769
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq90769
    | exact resolve eq90769 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90769
  have eq90824 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq83903 eq90804
    | exact resolve eq90804 eq83903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90804
  have eq90981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq90824 eq950
    | exact resolve eq950 eq90824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq90824
  have eq91063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq90981
  have eq91115 : x = (M.op y y) := by
    first
    | (have r₁ := eq91063
       have r₂ := eq28
       grind)
    | exact resolve eq91063 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91063
  have eq91203 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq89131
       have i₂ := eq91115
       grind)
    | exact superpose eq91115 eq89131
    | exact resolve eq89131 eq91115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89131
  have eq91204 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq83980 y X0
       have i₂ := eq91115
       grind)
    | exact superpose eq91115 eq83980
    | exact resolve eq83980 eq91115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83980 eq91115
  have eq91296 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq91203
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq91203
    | exact resolve eq91203 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91203
  have eq91552 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq91204 y
       grind)
    | exact superpose eq91204 eq19
    | (have j1 := eq91204 y
       grind)
    | exact resolve eq19 eq91204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq91602 : y = (M.op x x) := by
    first
    | exact superpose eq83976 eq91552
    | exact resolve eq91552 eq83976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91552
  have eq91671 : ∀ X0 : G, y = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq91602
       have i₂ := eq91204 X0
       grind)
    | (have i₁ := eq91602
       have i₂ := eq91204 x
       grind)
    | exact superpose eq91204 eq91602
    | exact resolve eq91602 eq91204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91204
  have eq91691 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq77148
       have i₂ := eq91602
       grind)
    | exact superpose eq91602 eq77148
    | exact resolve eq77148 eq91602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77148 eq91602
  have eq91831 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq91691
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq91691
    | exact resolve eq91691 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91691
  have eq91869 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq83903 eq91831
    | exact resolve eq91831 eq83903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91831
  have eq92880 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq91296 eq410
    | exact resolve eq410 eq91296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq91296
  have eq98018 : ∀ X0 : G, (σ y) = (σ (k X0 x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq7210 X0
       have i₂ := eq91671 X0
       grind)
    | exact superpose eq91671 eq7210
    | (have j0 := eq7210 X0
       grind)
    | exact resolve eq7210 eq91671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7210
  have eq98019 : ∀ X0 : G, (σ y) = (σ (k X0 x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq98018 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq98018
    | (have j0 := eq98018 X0
       grind)
    | exact resolve eq98018 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98018
  have eq98020 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq83903 eq98019
    | (have j0 := eq98019 X0
       grind)
    | exact resolve eq98019 eq83903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98019
  have eq98104 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 x)
       have i₂ := eq98020 X0
       grind)
    | exact superpose eq98020 eq16
    | (have j1 := eq98020 X0
       grind)
    | exact resolve eq16 eq98020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98020
  have eq98206 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq31 eq98104
    | (have j0 := eq98104 X0
       grind)
    | exact resolve eq98104 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq98104
  have eq98264 : ∀ X0 : G, y = (k X0 x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq83976 eq98206
    | (have j0 := eq98206 X0
       grind)
    | exact resolve eq98206 eq83976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83976 eq98206
  have eq98408 : ∀ X0 : G, x ≠ y ∨ (k x X0) = (M.op X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7232 x X0
       have i₂ := eq98264 x
       grind)
    | exact superpose eq98264 eq7232
    | (have j0 := eq7232 x X0
       have j1 := eq98264 x
       grind)
    | exact resolve eq7232 eq98264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7232 eq98264
  have eq98492 : ∀ X0 : G, x ≠ y ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq98408 X0
       have j1 := eq13 x X0
       grind)
    | (have r₁ := eq98408 X0
       have r₂ := eq13 x x
       grind)
    | exact resolve eq98408 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98408
  have eq98701 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq83907 eq92880
    | (have j0 := eq92880 (σ y) X0
       grind)
    | exact resolve eq92880 eq83907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92880
  have eq100382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq98701 eq91869
    | exact resolve eq91869 eq98701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91869 eq98701
  have eq100440 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq100382
  have eq100489 : x = y := by
    first
    | (have r₁ := eq100440
       have r₂ := eq28
       grind)
    | exact resolve eq100440 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100440
  have eq100545 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq100489
       grind)
    | exact superpose eq100489 eq25
    | exact resolve eq25 eq100489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100658 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq98492 X0
       have i₂ := eq100489
       grind)
    | exact superpose eq100489 eq98492
    | (have j0 := eq98492 X0
       grind)
    | (have r₁ := eq98492 X0
       have r₂ := eq100489
       grind)
    | exact resolve eq98492 eq100489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98492 eq100489
  have eq100659 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq100658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100658
  have eq100755 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq83903 eq100545
    | exact resolve eq100545 eq83903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100545
  have eq100830 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq100755
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq100755
    | exact resolve eq100755 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq100755
  have eq100999 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq100830 eq83907
    | exact resolve eq83907 eq100830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83907
  have eq101461 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq100659 x
       grind)
    | exact superpose eq100659 eq44
    | exact resolve eq44 eq100659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq100659
  have eq101537 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq101461
       have i₂ := eq91671 x
       grind)
    | exact superpose eq91671 eq101461
    | exact resolve eq101461 eq91671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91671 eq101461
  have eq101614 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19041 eq101537
    | exact resolve eq101537 eq19041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19041 eq101537
  have eq101683 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq100830 eq101614
    | exact resolve eq101614 eq100830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100830 eq101614
  have eq101745 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq100999 eq101683
    | exact resolve eq101683 eq100999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100999 eq101683
  have eq101789 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq101745
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq101745
    | exact resolve eq101745 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq101745
  have eq101829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq83903 eq101789
    | exact resolve eq101789 eq83903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83903 eq101789
  have eq101865 : False := by grind
  exact eq101865

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_pyy_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq48 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq146 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq151 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq146 X0 X1
       have j1 := eq48 X0 X1
       grind)
    | (have r₁ := eq146 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq146 X0 X0
       have r₂ := eq48 X0 X0
       grind)
    | exact resolve eq146 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq146
  have eq323 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq151 (σ X0) (σ X1)
       grind)
    | exact superpose eq151 eq15
    | exact resolve eq15 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq151 X0 X1
       grind)
    | exact superpose eq151 eq323
    | exact resolve eq323 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq323
  have eq333 : False := by grind
  exact eq333

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyy_pyx_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq395 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq403 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq416 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq403
    | (have j0 := eq403 X0 X1
       grind)
    | exact resolve eq403 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq424 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq395
    | (have j0 := eq395 X0 X1
       grind)
    | exact resolve eq395 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq449 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 X1
       have i₂ := eq65 (τ X1)
       grind)
    | exact superpose eq65 eq416
    | (have j0 := eq416 X0 X1
       grind)
    | exact resolve eq416 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq450 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq449 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq465 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X1
       have i₂ := eq65 (σ X1)
       grind)
    | exact superpose eq65 eq424
    | (have j0 := eq424 X0 X1
       grind)
    | exact resolve eq424 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq466 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq465 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq495 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq450
    | exact resolve eq450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq526 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq495 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq495
    | (have j0 := eq495 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq754 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq466 x y
       grind)
    | exact superpose eq466 eq16
    | (have j1 := eq466 x y
       grind)
    | exact resolve eq16 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq768 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq754
       have i₂ := eq526 y x
       grind)
    | exact superpose eq526 eq754
    | (have j1 := eq526 (σ x) (σ y)
       grind)
    | (have r₁ := eq754
       have r₂ := eq526 y x
       grind)
    | (have r₁ := eq754
       have r₂ := eq526 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq754
       have r₂ := eq526 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq754 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq754
  have eq769 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq768
  have eq789 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq769
       grind)
    | exact superpose eq769 eq16
    | exact resolve eq16 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq790 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq789
       have i₂ := eq65 (σ x)
       grind)
    | exact superpose eq65 eq789
    | exact resolve eq789 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq791 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq790
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq790
    | exact resolve eq790 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq792 : (σ x) = (σ y) := by grind
  clear eq791
  have eq793 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq792
       grind)
    | exact superpose eq792 eq16
    | exact resolve eq16 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq792
       grind)
    | exact superpose eq792 eq10
    | exact resolve eq10 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq831 : x = y := by
    first
    | (have i₁ := eq794
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq794
    | exact resolve eq794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq832 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq793
       have i₂ := eq65 (σ x)
       grind)
    | exact superpose eq65 eq793
    | exact resolve eq793 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq833 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq832
       have i₂ := eq831
       grind)
    | exact superpose eq831 eq832
    | exact resolve eq832 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq832
  have eq834 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq833
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq833
    | exact resolve eq833 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq833
  have eq835 : False := by grind
  exact eq835

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,Y) = Y then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_y_pxy_pyy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq63 (M.op X0 X1)
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq383 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq386 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq384 X1 X0
       grind)
    | exact superpose eq384 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq384 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq384 X0 X1
       grind)
    | exact resolve eq12 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq384 (σ y) (σ x)
       grind)
    | exact superpose eq384 eq16
    | (have j1 := eq384 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq401 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq398
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq398
    | exact resolve eq398 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq404 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq400 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq400
    | exact resolve eq400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq400 (τ X0) X1
       grind)
    | exact superpose eq400 eq17
    | (have j1 := eq400 (τ X0) X1
       grind)
    | exact resolve eq17 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq400
  have eq554 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq429 X1 (τ X0)
       grind)
    | exact superpose eq429 eq18
    | (have j1 := eq429 X1 (τ X0)
       grind)
    | exact resolve eq18 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq429
  have eq559 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq571 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq572 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq571
    | (have j0 := eq571 X0 X1
       grind)
    | exact resolve eq571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq643 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq572 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq572
    | (have j0 := eq572 X1 (σ X0)
       grind)
    | exact resolve eq572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq818 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq643 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq643
    | (have j0 := eq643 X1 (σ X0)
       grind)
    | exact resolve eq643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq861 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq818 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq818
    | (have j0 := eq818 X0 X1
       grind)
    | exact resolve eq818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq864 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq861 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq861
    | (have j0 := eq861 X0 X1
       grind)
    | exact resolve eq861 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq1030 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq401
       have i₂ := eq384 y x
       grind)
    | exact superpose eq384 eq401
    | (have j1 := eq384 y x
       grind)
    | exact resolve eq401 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq1031 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq1030
  have eq1051 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq404 x y
       grind)
    | exact superpose eq404 eq16
    | (have j1 := eq404 x y
       grind)
    | exact resolve eq16 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq1078 : (σ y) = (σ (k x y)) := by
    first
    | (have j1 := eq864 y x
       grind)
    | (have r₁ := eq1051
       have r₂ := eq864 y x
       grind)
    | exact resolve eq1051 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq1051
  have eq1089 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1078
       grind)
    | exact superpose eq1078 eq10
    | exact resolve eq10 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : y = (k x y) := by
    first
    | (have i₁ := eq1089
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1089
    | exact resolve eq1089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1669 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1031
       have i₂ := eq1126
       grind)
    | exact superpose eq1126 eq1031
    | exact resolve eq1031 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq1126
  have eq1695 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq69 x y
       have i₂ := eq1669
       grind)
    | exact superpose eq1669 eq69
    | exact resolve eq69 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1797 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1695
       grind)
    | exact superpose eq1695 eq16
    | exact resolve eq16 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1835 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1797
       have i₂ := eq1669
       grind)
    | exact superpose eq1669 eq1797
    | exact resolve eq1797 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq1797
  have eq1837 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1835
  have eq1841 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq401
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq401
    | exact resolve eq401 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq1837
  have eq1857 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1841
  have eq1862 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1857
       have i₂ := eq1078
       grind)
    | exact superpose eq1078 eq1857
    | exact resolve eq1857 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq1857
  have eq1863 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1862
  have eq1866 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1863
       grind)
    | exact superpose eq1863 eq16
    | exact resolve eq16 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1874 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq69 (σ x) (σ y)
       have i₂ := eq1863
       grind)
    | exact superpose eq1863 eq69
    | exact resolve eq69 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1897 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1874
       have i₂ := eq1863
       grind)
    | exact superpose eq1863 eq1874
    | exact resolve eq1874 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq1917 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1863
       have i₂ := eq1897
       grind)
    | exact superpose eq1897 eq1863
    | exact resolve eq1863 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863 eq1897
  have eq1959 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1917
       grind)
    | exact superpose eq1917 eq10
    | exact resolve eq10 eq1917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq2000 : x = y := by
    first
    | (have i₁ := eq1959
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1959
    | exact resolve eq1959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq2019 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1866
       have i₂ := eq2000
       grind)
    | exact superpose eq2000 eq1866
    | exact resolve eq1866 eq2000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866 eq2000
  have eq2022 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2019
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq2019
    | exact resolve eq2019 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2019
  have eq2023 : False := by grind
  exact eq2023

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pxy_pyx_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq98 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq98 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq98 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq107 (σ X0) (σ X1)
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 X1
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq112
    | exact resolve eq112 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq112
  have eq237 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq121 x y
       grind)
    | exact superpose eq121 eq16
    | (have r₁ := eq16
       have r₂ := eq121 x y
       grind)
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq246 : False := by grind
  exact eq246
