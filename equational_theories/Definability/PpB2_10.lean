import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_x_pxy_Equation2045 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq108 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq326 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X0) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X3
       have i₂ := eq108 X0 X1 X2
       grind)
    | (have i₁ := eq9 X1 (M.op X1 X2) X2
       have i₂ := eq108 X1 X1 X2
       grind)
    | exact superpose eq108 eq9
    | exact resolve eq9 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X3) X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq113 X0 X3 X4
       have i₂ := eq108 X0 X1 X2
       grind)
    | (have i₁ := eq113 X2 X1 X2
       have i₂ := eq108 X2 X2 X2
       grind)
    | exact superpose eq108 eq113
    | exact resolve eq113 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq113
  have eq1360 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) X3)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq326 X0 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq326 X1 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq326
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq326 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq1398 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1360 X0 X1 x x
       have i₂ := eq484 X0 X1 x X1 x
       grind)
    | exact superpose eq484 eq1360
    | (have j0 := eq1360 X0 X1 x x
       grind)
    | exact resolve eq1360 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq1360
  have eq1399 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1398 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1443 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1399 X0 (τ X1)
       grind)
    | exact superpose eq1399 eq19
    | (have j1 := eq1399 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1445 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1399 (σ X0) (σ X1)
       grind)
    | exact superpose eq1399 eq15
    | (have j1 := eq1399 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1516 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1443 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1443
    | exact resolve eq1443 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443
  have eq1555 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1516 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1516
    | (have j0 := eq1516 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq1516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq3279 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1445 x y
       grind)
    | exact superpose eq1445 eq16
    | (have j1 := eq1445 x y
       grind)
    | exact resolve eq16 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq3337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3279
       have i₂ := eq1555 y x
       grind)
    | exact superpose eq1555 eq3279
    | (have j1 := eq1555 (σ x) (σ y)
       grind)
    | (have r₁ := eq3279
       have r₂ := eq1555 y x
       grind)
    | (have r₁ := eq3279
       have r₂ := eq1555 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3279
       have r₂ := eq1555 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3279 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555 eq3279
  have eq3338 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3337
  have eq3343 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3338
       grind)
    | exact superpose eq3338 eq10
    | exact resolve eq10 eq3338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3387 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3343
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3343
    | exact resolve eq3343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3388 : x = y := by grind
  clear eq3387
  have eq3390 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3388
       grind)
    | exact superpose eq3388 eq16
    | exact resolve eq16 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388
  have eq3391 : False := by grind
  exact eq3391

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pxy_x_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  clear eq24 eq35
  have eq64 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
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
  have eq69 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq115
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq143 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq65
    | exact resolve eq65 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq144 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq69
    | (have r₁ := eq69
       have r₂ := eq129
       grind)
    | exact resolve eq69 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq129
  have eq338 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq337
  have eq339 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq338
       have r₂ := eq143
       grind)
    | exact resolve eq338 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq338
  have eq342 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq339 eq116
    | exact resolve eq116 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq339
  have eq346 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq342
  have eq351 : x = (M.op x y) := by
    first
    | (have r₁ := eq346
       have r₂ := eq144
       grind)
    | exact resolve eq346 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq346
  have eq354 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq351 eq20
    | exact resolve eq20 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq357 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq351 eq64
    | exact resolve eq64 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq358 : x ≠ x ∨ x = y ∨ x = (k x y) := by
    first
    | exact superpose eq351 eq68
    | (have r₁ := eq68
       have r₂ := eq351
       grind)
    | exact resolve eq68 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq351
  have eq363 : x = y ∨ x = (k x y) := by grind
  clear eq358
  have eq369 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq354
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq354
    | exact resolve eq354 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq397 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq369 eq26
    | exact resolve eq26 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq572 : x = (k x y) := by
    first
    | (have r₁ := eq363
       have r₂ := eq357
       grind)
    | exact resolve eq363 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq363
  have eq576 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq572
       grind)
    | exact superpose eq572 eq44
    | exact resolve eq44 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq572
  have eq583 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq369 eq576
    | exact resolve eq576 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq585 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq583
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq583
    | exact resolve eq583 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq583
  have eq586 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq369 eq585
    | exact resolve eq585 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq585
  have eq589 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq586 eq84
    | (have j0 := eq84 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq84 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq586
  have eq590 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq589
  have eq592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq397 eq590
    | exact resolve eq590 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq590
  have eq595 : False := by grind
  exact eq595

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq296 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq305 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq306 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq311 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq306
    | (have j0 := eq306 X0 X1
       grind)
    | exact resolve eq306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq312 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq867 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq312
    | exact resolve eq312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq312 x y
       grind)
    | exact superpose eq312 eq16
    | (have j1 := eq312 x y
       grind)
    | exact resolve eq16 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq905 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq867 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq867
    | (have j0 := eq867 X0 X1
       grind)
    | exact resolve eq867 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq867
  have eq907 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq905
    | exact resolve eq905 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq966 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq907 (τ X0) X1
       grind)
    | exact superpose eq907 eq18
    | (have j1 := eq907 (τ X0) X1
       grind)
    | exact resolve eq18 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq907
  have eq2503 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq966 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq966
    | exact resolve eq966 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq2565 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2503 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2503
    | (have j0 := eq2503 X0 X1
       grind)
    | exact resolve eq2503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq2743 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq875
       have i₂ := eq2565 x y
       grind)
    | exact superpose eq2565 eq875
    | (have j1 := eq2565 (σ x) (σ y)
       grind)
    | (have r₁ := eq875
       have r₂ := eq2565 x y
       grind)
    | exact resolve eq875 eq2565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2744 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2743
  have eq2750 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2744
  have eq2796 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq875
       have i₂ := eq2750
       grind)
    | exact superpose eq2750 eq875
    | exact resolve eq875 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq2750
  have eq2797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2796
  have eq2798 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2797
  have eq2891 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq2798
  have eq2939 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq2891
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2891
    | exact resolve eq2891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891
  have eq3167 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2939
       grind)
    | exact superpose eq2939 eq16
    | exact resolve eq16 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq3379 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3167
       have i₂ := eq2565 x y
       grind)
    | exact superpose eq2565 eq3167
    | (have j1 := eq2565 x y
       grind)
    | (have r₁ := eq3167
       have r₂ := eq2565 x y
       grind)
    | exact resolve eq3167 eq2565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq3380 : x = (M.op y y) := by grind
  clear eq3379
  have eq3385 : (M.op x y) = (k x y) := by grind
  clear eq3380
  have eq3514 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq3167
       have i₂ := eq3385
       grind)
    | exact superpose eq3385 eq3167
    | exact resolve eq3167 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167 eq3385
  have eq3517 : False := by grind
  exact eq3517

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pxx_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq14 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq44
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq116 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq116 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq43
    | exact resolve eq43 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq123 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq84
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq84
    | exact resolve eq84 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq124 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq123
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq123
    | exact resolve eq123 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq120
  have eq475 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 : G, (M.op (M.op x x) x) = (M.op (M.op x y) (M.op X0 (M.op (M.op x x) x))) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y) X0
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq107 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq924
    | exact resolve eq924 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq928 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq925
       have r₂ := eq27
       grind)
    | exact resolve eq925 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq930 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq928
    | exact resolve eq928 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq937 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq930 eq54
    | exact resolve eq54 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq938 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq930 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq930
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq930
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq930
       grind)
    | exact resolve eq12 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq930 eq14
    | exact resolve eq14 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq942 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq938
       have r₂ := eq26
       grind)
    | exact resolve eq938 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1047 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq942 eq107
    | exact resolve eq107 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq1050 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1047
  have eq1058 : (τ (σ y)) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1050 eq124
    | exact resolve eq124 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq1059 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1050 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1050
       grind)
    | exact resolve eq13 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1071 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1059 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1073 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1058
    | exact resolve eq1058 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1058
  have eq1160 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq940 sF2
       have i₂ := eq475 sF2 x
       grind)
    | (have i₁ := eq940 sF2
       have i₂ := eq475 sF2 sF2
       grind)
    | exact superpose eq475 eq940
    | exact resolve eq940 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq1162 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq937 sF4
       have i₂ := eq475 sF4 x
       grind)
    | (have i₁ := eq937 sF4
       have i₂ := eq475 sF4 sF4
       grind)
    | exact superpose eq475 eq937
    | exact resolve eq937 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq1191 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq1160
    | (have j0 := eq1160 (σ y)
       grind)
    | exact resolve eq1160 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1212 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1191 eq1162
    | exact resolve eq1162 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq1191
  have eq1222 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1212
  have eq1224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1222 eq1073
    | exact resolve eq1073 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq1224
  have eq1251 : (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1247
       have r₂ := eq27
       grind)
    | exact resolve eq1247 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1254 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1251
       grind)
    | exact superpose eq1251 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1251
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1251
       grind)
    | exact resolve eq12 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1260 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) := by grind
  clear eq1254
  have eq1261 : (k x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1260
       have r₂ := eq18
       grind)
    | exact resolve eq1260 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1260
  have eq1428 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1261
       grind)
    | exact superpose eq1261 eq44
    | exact resolve eq44 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1261
  have eq1431 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1428
       have i₂ := eq127
       grind)
    | exact superpose eq127 eq1428
    | exact resolve eq1428 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1439 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1431 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1431
  have eq1440 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1439
    | exact resolve eq1439 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1443 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1440
    | exact resolve eq1440 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq13891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1071 eq107
    | exact resolve eq107 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1071
  have eq13906 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq13891
  have eq13917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13906
    | exact resolve eq13906 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13906
  have eq13919 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq13917
       have r₂ := eq27
       grind)
    | exact resolve eq13917 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13917
  have eq13925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq13919 eq1222
    | exact resolve eq1222 eq13919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222 eq13919
  have eq13998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq13925
  have eq14003 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq13998
       have r₂ := eq27
       grind)
    | exact resolve eq13998 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13998
  have eq14011 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq14003
       grind)
    | exact superpose eq14003 eq14
    | exact resolve eq14 eq14003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14013 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq54 x y x
       have i₂ := eq14003
       grind)
    | exact superpose eq14003 eq54
    | exact resolve eq54 eq14003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq14483 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq14013 sF0
       have i₂ := eq475 sF0 x
       grind)
    | (have i₁ := eq14013 sF0
       have i₂ := eq475 sF0 sF0
       grind)
    | exact superpose eq475 eq14013
    | exact resolve eq14013 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14013
  have eq14841 : (M.op x y) = (M.op (M.op (M.op (M.op x x) x) (M.op x y)) x) := by
    first
    | exact superpose eq582 eq14483
    | exact resolve eq14483 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq14483
  have eq14877 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq14011 eq14841
    | exact resolve eq14841 eq14011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14841
  have eq15135 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq14877
       grind)
    | exact superpose eq14877 eq127
    | exact resolve eq127 eq14877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq15145 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14011 X0
       have i₂ := eq14877
       grind)
    | exact superpose eq14877 eq14011
    | exact resolve eq14011 eq14877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14011 eq14877
  have eq15213 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq15135
    | exact resolve eq15135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15135
  have eq15234 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ (M.op x y)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq15213 eq583
    | exact resolve eq583 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq15265 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq15213 eq14
    | exact resolve eq14 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16514 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1443 eq15265
    | exact resolve eq15265 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443 eq15265
  have eq16623 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq15213 eq16514
    | (have j0 := eq16514 X0
       grind)
    | exact resolve eq16514 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16514
  have eq16629 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq16623 X0
       grind)
    | (have r₁ := eq16623 X0
       have r₂ := eq27
       grind)
    | exact resolve eq16623 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16623
  have eq19044 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15234 eq475
    | exact resolve eq475 eq15234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq15234
  have eq19266 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq19044 eq14
    | exact resolve eq14 eq19044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19044
  have eq19659 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16629 eq19266
    | exact resolve eq19266 eq16629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19266
  have eq19779 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f19779_13 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op y y) := by
      intro X0
      grind
    have f19779_14 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
      intro X0
      grind
    have f19779_22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
    have f19779_24 : y ≠ (M.op y y) := by grind
    have f19779_26 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) := by
      intro X0
      first
      | (have j0 := f19779_14 X0
         grind)
      | (have r₁ := f19779_14 X0
         have r₂ := f19779_24
         grind)
      | exact resolve f19779_14 f19779_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f19779_27 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
      intro X0
      first
      | (have j0 := f19779_13 X0
         grind)
      | (have r₁ := f19779_13 X0
         have r₂ := f19779_24
         grind)
      | exact resolve f19779_13 f19779_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f19779_41 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
      first
      | (have i₁ := f19779_27 (M.op (σ (M.op x y)) x)
         have i₂ := f19779_26 x
         grind)
      | exact superpose f19779_26 f19779_27
      | exact resolve f19779_27 f19779_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f19779_43 : False := by
      first
      | (have r₁ := f19779_41
         have r₂ := f19779_22
         grind)
      | exact resolve f19779_41 f19779_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f19779_43
  clear eq16629 eq19659
  have eq19842 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq19779
  have eq19852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15213 eq19842
    | exact resolve eq19842 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19842
  have eq19858 : y = (M.op y y) := by
    first
    | (have r₁ := eq19852
       have r₂ := eq27
       grind)
    | exact resolve eq19852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19852
  have eq19863 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq19858
       grind)
    | exact superpose eq19858 eq52
    | exact resolve eq52 eq19858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq20153 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq19863 x
       have i₂ := eq14003
       grind)
    | exact superpose eq14003 eq19863
    | exact resolve eq19863 eq14003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14003
  have eq20158 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq19863 y
       have i₂ := eq19858
       grind)
    | exact superpose eq19858 eq19863
    | exact resolve eq19863 eq19858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19858 eq19863
  have eq20225 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20153 eq15145
    | exact resolve eq15145 eq20153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15145 eq20153
  have eq20416 : x = y := by
    first
    | exact superpose eq20158 eq20225
    | exact resolve eq20225 eq20158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20158 eq20225
  have eq20418 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq20416
       grind)
    | exact superpose eq20416 eq24
    | exact resolve eq24 eq20416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq20416
  have eq20475 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20418
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20418
    | exact resolve eq20418 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20418
  have eq20931 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20475 eq26
    | exact resolve eq26 eq20475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq20475
  have eq20990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15213 eq20931
    | exact resolve eq20931 eq15213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15213 eq20931
  have eq20996 : False := by grind
  exact eq20996

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
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
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq60
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq69
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
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq90
  have eq516 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
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
  have eq525 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq516 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq530 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq525 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq525 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq525 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq543 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq530 X0 X1
       have j1 := eq80 X1 (σ X0)
       grind)
    | (have r₁ := eq530 X0 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq530 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq530
  have eq551 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq543 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq543
    | (have j0 := eq543 X0 X1
       grind)
    | exact resolve eq543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq552 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq551 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq558 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq552 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq552
    | exact resolve eq552 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq552 x y
       grind)
    | exact superpose eq552 eq16
    | exact resolve eq16 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq702 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq558 X0 (τ X1)
       grind)
    | exact superpose eq558 eq18
    | exact resolve eq18 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq558
  have eq719 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq702
    | exact resolve eq702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq727 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq719 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq719
    | exact resolve eq719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq739 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq569
       have i₂ := eq727 x y
       grind)
    | exact superpose eq727 eq569
    | exact resolve eq569 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq727
  have eq740 : False := by grind
  exact eq740

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq82 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 (k X1 X0) (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq89 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq91 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq82 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq90 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq90 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq1298 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1299 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1314 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1299 (σ X0) (σ X1)
       grind)
    | exact superpose eq1299 eq15
    | (have j1 := eq1299 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1323 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq1299 (τ X0) (τ X1)
       grind)
    | exact superpose eq1299 eq32
    | (have j1 := eq1299 (τ X0) (τ X1)
       grind)
    | exact resolve eq32 eq1299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1299
  have eq1552 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1314 x y
       grind)
    | exact superpose eq1314 eq16
    | (have j1 := eq1314 x y
       grind)
    | exact resolve eq16 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1632 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq1323 X0 X1
       grind)
    | (have i₁ := eq11 X0
       have i₂ := eq1323 X0 X1
       grind)
    | exact superpose eq1323 eq11
    | (have j1 := eq1323 X0 X1
       grind)
    | exact resolve eq11 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1660 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1632 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1632
    | (have j0 := eq1632 X0 X1
       grind)
    | exact resolve eq1632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1701 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1660 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1660
    | (have j0 := eq1660 (τ (k X1 (σ X0))) (M.op (τ X1) X0)
       grind)
    | exact resolve eq1660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1736 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1701 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq1701
    | (have j0 := eq1701 X0 X1
       grind)
    | exact resolve eq1701 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1701
  have eq1744 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1736 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1736
    | (have j0 := eq1736 X0 (σ X1)
       grind)
    | exact resolve eq1736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1795 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1552
       have i₂ := eq1744 x y
       grind)
    | exact superpose eq1744 eq1552
    | (have j1 := eq1744 x y
       grind)
    | (have r₁ := eq1552
       have r₂ := eq1744 (M.op x y) (k x y)
       grind)
    | (have r₁ := eq1552
       have r₂ := eq1744 (k x y) (M.op x y)
       grind)
    | exact resolve eq1552 eq1744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552 eq1744
  have eq1796 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq1795
  have eq1797 : (σ x) = (σ y) := by grind
  clear eq1796
  have eq1805 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1797
       grind)
    | exact superpose eq1797 eq10
    | exact resolve eq10 eq1797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1807 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1797
       grind)
    | exact superpose eq1797 eq15
    | exact resolve eq15 eq1797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq1840 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1807 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq1807
    | exact resolve eq1807 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq1842 : x = y := by
    first
    | (have i₁ := eq1805
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1805
    | exact resolve eq1805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq1843 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1842
       grind)
    | exact superpose eq1842 eq16
    | exact resolve eq16 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1932 : (σ (k y x)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1840
  have eq1995 : (σ (M.op x x)) = (σ (k x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1932
       have i₂ := eq1842
       grind)
    | exact superpose eq1842 eq1932
    | exact resolve eq1932 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq2002 : x = (M.op x x) ∨ (σ (M.op x x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq1995
       have i₂ := eq1842
       grind)
    | exact superpose eq1842 eq1995
    | exact resolve eq1995 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842 eq1995
  have eq2230 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1843
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq1843
    | (have j1 := eq71 x
       grind)
    | exact resolve eq1843 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2264 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2878 : (M.op x x) = (k x x) ∨ (σ (M.op x x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq92 x
       have i₂ := eq2002
       grind)
    | exact superpose eq2002 eq92
    | exact resolve eq92 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6801 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq2264 x
       have i₂ := eq2878
       grind)
    | exact superpose eq2878 eq2264
    | (have j0 := eq2264 x
       grind)
    | exact resolve eq2264 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264 eq2878
  have eq6811 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq6801
       have r₂ := eq2230
       grind)
    | exact resolve eq6801 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801
  have eq6812 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq6811
       have i₂ := eq2002
       grind)
    | exact superpose eq2002 eq6811
    | exact resolve eq6811 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6811
  have eq6815 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (k x x)) := by grind
  clear eq6812
  have eq6816 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq6815
       have r₂ := eq2230
       grind)
    | exact resolve eq6815 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230 eq6815
  have eq6819 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1843
       have i₂ := eq6816
       grind)
    | exact superpose eq6816 eq1843
    | exact resolve eq1843 eq6816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq6825 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq92 (σ x)
       have i₂ := eq6816
       grind)
    | exact superpose eq6816 eq92
    | exact resolve eq92 eq6816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq6867 : (σ (k x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6825
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6825
    | exact resolve eq6825 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825
  have eq6871 : (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq6867
       have i₂ := eq6816
       grind)
    | exact superpose eq6816 eq6867
    | exact resolve eq6867 eq6816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6816 eq6867
  have eq6872 : (σ x) ≠ (σ x) ∨ (σ (M.op x x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq6819
       have i₂ := eq2002
       grind)
    | exact superpose eq2002 eq6819
    | exact resolve eq6819 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq6875 : (σ (M.op x x)) = (σ (k x x)) := by grind
  clear eq6872
  have eq6876 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6875
       have i₂ := eq6871
       grind)
    | exact superpose eq6871 eq6875
    | exact resolve eq6875 eq6871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6871 eq6875
  have eq6877 : False := by grind
  exact eq6877

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq47 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1 x
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq47
    | (have j0 := eq47 X0 X1 x
       grind)
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq88 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq56
    | (have j0 := eq56 X0 X1
       have j1 := eq51 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq56
  have eq3417 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq273 x y
       grind)
    | exact superpose eq273 eq16
    | (have j1 := eq273 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq273 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq273 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq273 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq3494 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3417
  have eq4625 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) X0) (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq88 y x
       have i₂ := eq3494
       grind)
    | exact superpose eq3494 eq88
    | exact resolve eq88 eq3494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3494
  have eq4670 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4625 x
       have i₂ := eq88 x x
       grind)
    | exact superpose eq88 eq4625
    | exact resolve eq4625 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq4625
  have eq4671 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4670
  have eq6708 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4671
       grind)
    | exact superpose eq4671 eq10
    | exact resolve eq10 eq4671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq6741 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6708
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6708
    | exact resolve eq6708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6708
  have eq6742 : x = y := by grind
  clear eq6741
  have eq9294 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6742
       grind)
    | exact superpose eq6742 eq16
    | exact resolve eq16 eq6742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6742
  have eq9295 : False := by grind
  exact eq9295

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_y_pxy_Equation2046 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (σ y) = (M.op (M.op (k (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq178
    | exact resolve eq178 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq182 : ∀ X0 : G, y = (M.op (M.op (k y y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op X0 X0)
       have i₂ := eq174 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (k (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq188
    | exact resolve eq188 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq649 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq187 (M.op (k X0 X0) X0) X1
       have i₂ := eq191 X0
       grind)
    | exact superpose eq191 eq187
    | exact resolve eq187 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq191
  have eq659 : (M.op (k x x) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq649 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq649
    | (have j0 := eq649 x y
       grind)
    | exact resolve eq649 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : (M.op (k (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq649
    | (have j0 := eq649 (σ x) (σ y)
       grind)
    | exact resolve eq649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq186 x x X0
       have i₂ := eq659
       grind)
    | exact superpose eq659 eq186
    | exact resolve eq186 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq689 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq660 eq186
    | exact resolve eq186 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq660
  have eq749 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq750 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1194 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq749
       grind)
    | exact superpose eq749 eq40
    | exact resolve eq40 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1195 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1194
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1194
    | exact resolve eq1194 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1197 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq1195
    | exact resolve eq1195 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1197 eq750
    | exact resolve eq750 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1241 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq1234
       have r₂ := eq27
       grind)
    | exact resolve eq1234 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1249 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1241 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1241
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1241
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1241
       grind)
    | exact resolve eq12 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1259 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq1249
  have eq1267 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq1259
       have r₂ := eq26
       grind)
    | exact resolve eq1259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1273 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1267 eq1197
    | exact resolve eq1197 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq1267
  have eq1279 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1273
  have eq1290 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq683 y
       have i₂ := eq1279
       grind)
    | exact superpose eq1279 eq683
    | exact resolve eq683 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq1297 : (M.op (k y y) y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq649 y x
       have i₂ := eq1279
       grind)
    | exact superpose eq1279 eq649
    | exact resolve eq649 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1313 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1290
       have i₂ := eq649 sF0 x
       grind)
    | exact superpose eq649 eq1290
    | exact resolve eq1290 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq2834 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq1297
       grind)
    | exact superpose eq1297 eq182
    | exact resolve eq182 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1297
  have eq2860 : y = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2834
       have i₂ := eq649 sF0 y
       grind)
    | exact superpose eq649 eq2834
    | exact resolve eq2834 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834
  have eq2862 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1313 eq2860
    | exact resolve eq2860 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313 eq2860
  have eq2863 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq2862
  have eq2865 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2863 eq31
    | exact resolve eq31 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2890 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq2865
    | exact resolve eq2865 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2865
  have eq2891 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq2890
  have eq2893 : (M.op x y) = (τ (σ y)) ∨ x = y := by
    first
    | exact superpose eq2891 eq28
    | exact resolve eq28 eq2891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2918 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq2893
    | exact resolve eq2893 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2893
  have eq2921 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq2918
       grind)
    | exact superpose eq2918 eq18
    | exact resolve eq18 eq2918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2929 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq749
       have i₂ := eq2918
       grind)
    | exact superpose eq2918 eq749
    | exact resolve eq749 eq2918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq2939 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq2918
  have eq2946 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have r₁ := eq2929
       have r₂ := eq2939
       grind)
    | exact resolve eq2929 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq2954 : (M.op x y) ≠ (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2921 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | exact resolve eq12 eq2921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq2981 : x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq2954
       have r₂ := eq2946
       grind)
    | exact resolve eq2954 eq2946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946 eq2954
  have eq2983 : (M.op x y) = (k x (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq2981
       have r₂ := eq2939
       grind)
    | exact resolve eq2981 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939 eq2981
  have eq2985 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2983 eq35
    | exact resolve eq35 eq2983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2983
  have eq2988 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq2985
    | exact resolve eq2985 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985
  have eq2990 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2891 eq2988
    | exact resolve eq2988 eq2891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891 eq2988
  have eq2996 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2990 eq750
    | exact resolve eq750 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq2990
  have eq3725 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2996 eq689
    | exact resolve eq689 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq3734 : (M.op (k (σ y) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2996 eq649
    | exact resolve eq649 eq2996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq3755 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3725
       have i₂ := eq649 sF4 sF2
       grind)
    | exact superpose eq649 eq3725
    | exact resolve eq3725 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq5956 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3734 eq181
    | exact resolve eq181 eq3734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq3734
  have eq5987 : (σ y) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5956
       have i₂ := eq649 sF4 sF3
       grind)
    | exact superpose eq649 eq5956
    | exact resolve eq5956 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq5956
  have eq5989 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3755 eq5987
    | exact resolve eq5987 eq3755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3755 eq5987
  have eq5990 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5989
  have eq5991 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5990 eq27
    | exact resolve eq27 eq5990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5990
  have eq6031 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq5991
       have r₂ := eq2863
       grind)
    | exact resolve eq5991 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863 eq5991
  have eq6033 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq6031 eq31
    | exact resolve eq31 eq6031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq6031
  have eq6063 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq6033
    | exact resolve eq6033 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6033
  have eq6064 : x = y := by grind
  clear eq6063
  have eq6078 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6064
       grind)
    | exact superpose eq6064 eq18
    | exact resolve eq18 eq6064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6079 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6064
       grind)
    | exact superpose eq6064 eq24
    | exact resolve eq24 eq6064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6064
  have eq6088 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq6079
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6079
    | exact resolve eq6079 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079
  have eq6089 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq6078
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq6078
    | exact resolve eq6078 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6078
  have eq6090 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6088 eq26
    | exact resolve eq26 eq6088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6088
  have eq6117 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6090
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq6090
    | exact resolve eq6090 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq6090
  have eq6127 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq6089
       grind)
    | exact superpose eq6089 eq39
    | exact resolve eq39 eq6089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq6089
  have eq6138 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6127
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6127
    | exact resolve eq6127 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6127
  have eq6141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6117 eq6138
    | exact resolve eq6138 eq6117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6117 eq6138
  have eq6143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6141
    | exact resolve eq6141 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6141
  have eq6145 : False := by grind
  exact eq6145
