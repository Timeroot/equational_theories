import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq51 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq15
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq65
    | exact resolve eq65 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq65
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq89
    | (have j0 := eq89 (σ X0) (σ X1)
       grind)
    | exact resolve eq89 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq10
    | (have j1 := eq90 X0 X1
       grind)
    | exact resolve eq10 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq497 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq476
    | (have j0 := eq476 X0 X1
       grind)
    | exact resolve eq476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq532 : x = y ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq497 y x
       grind)
    | exact superpose eq497 eq16
    | (have j1 := eq497 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq497 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq497 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq553 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq532
       grind)
    | exact superpose eq532 eq16
    | exact resolve eq16 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq554 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have r₁ := eq553
       have r₂ := eq74 x
       grind)
    | exact resolve eq553 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq554
       have i₂ := eq89 y x
       grind)
    | exact superpose eq89 eq554
    | (have j1 := eq89 x y
       grind)
    | (have r₁ := eq554
       have r₂ := eq89 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq554
       have r₂ := eq89 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq554 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq554
  have eq568 : x = y := by grind
  clear eq565
  have eq663 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq568
       grind)
    | exact superpose eq568 eq16
    | exact resolve eq16 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq664 : False := by grind
  exact eq664

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation3690 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq89 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (M.op x x) = (k y x) := by
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
  have eq90 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq11743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11743
    | exact resolve eq11743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11743
  have eq11755 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11744
       have r₂ := eq28
       grind)
    | exact resolve eq11744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11744
  have eq11759 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11755
    | exact resolve eq11755 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11755
  have eq11766 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11759 eq90
    | (have r₁ := eq90
       have r₂ := eq11759
       grind)
    | exact resolve eq90 eq11759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq11759
  have eq11851 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11766
  have eq11852 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11851
  have eq12213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11852 eq113
    | exact resolve eq113 eq11852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq11852
  have eq12222 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12213
  have eq12225 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12222
       have r₂ := eq28
       grind)
    | exact resolve eq12222 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12222
  have eq12227 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq12225
       grind)
    | exact superpose eq12225 eq52
    | exact resolve eq52 eq12225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq12229 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq12225
       grind)
    | exact superpose eq12225 eq89
    | (have r₁ := eq89
       have r₂ := eq12225
       grind)
    | exact resolve eq89 eq12225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq12225
  have eq12316 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq12229
  have eq12317 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12316
  have eq12368 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq12227
    | exact resolve eq12227 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12227
  have eq12390 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq12317
       grind)
    | exact superpose eq12317 eq98
    | exact resolve eq98 eq12317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq12317
  have eq12406 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq12390
    | exact resolve eq12390 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12390
  have eq13480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12406 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12406
  have eq13481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13480
  have eq13485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq13481
    | exact resolve eq13481 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13481
  have eq13496 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13485
       have r₂ := eq28
       grind)
    | exact resolve eq13485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13485
  have eq13500 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq13496
    | exact resolve eq13496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13496
  have eq13638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13500 eq12368
    | exact resolve eq12368 eq13500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12368 eq13500
  have eq13722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13638
  have eq13758 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13722
       have r₂ := eq28
       grind)
    | exact resolve eq13722 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13722
  have eq13794 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq13758 eq30
    | exact resolve eq30 eq13758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13758
  have eq13886 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq13794
    | exact resolve eq13794 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13794
  have eq13887 : x = y := by grind
  clear eq13886
  have eq13906 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13887
       grind)
    | exact superpose eq13887 eq19
    | exact resolve eq19 eq13887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq13907 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq13887
       grind)
    | exact superpose eq13887 eq25
    | exact resolve eq25 eq13887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq13887
  have eq14004 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13907
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13907
    | exact resolve eq13907 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13907
  have eq14020 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14004 eq27
    | exact resolve eq27 eq14004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14004
  have eq14573 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14020 eq74
    | exact resolve eq74 eq14020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq14020
  have eq14714 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14573
       have i₂ := eq13906
       grind)
    | exact superpose eq13906 eq14573
    | exact resolve eq14573 eq13906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13906 eq14573
  have eq14775 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14714 eq15
    | exact resolve eq15 eq14714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14714
  have eq14818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq14775
    | exact resolve eq14775 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq14775
  have eq14831 : False := by grind
  exact eq14831

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_pyy_pxy_pxx_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
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
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
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
  have eq179 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq188 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq199 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X0 X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 x
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq16
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq190 (M.op X0 X1)
       grind)
    | exact superpose eq190 eq16
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (k X1 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq201 X0 X1
       have i₂ := eq190 X1
       grind)
    | exact superpose eq190 eq201
    | exact resolve eq201 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq207 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 y
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op (M.op x y) (M.op x X0)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq13
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq212 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq222 : (k (M.op x y) (M.op x y)) = (M.op y y) := by
    first
    | (have i₁ := eq207
       have i₂ := eq190 sF0
       grind)
    | exact superpose eq190 eq207
    | exact resolve eq207 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq224 : (k y y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq222
       have i₂ := eq190 y
       grind)
    | exact superpose eq190 eq222
    | exact resolve eq222 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq227 : (k (σ y) (σ y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq224
       grind)
    | exact superpose eq224 eq40
    | exact resolve eq40 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq228 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq227
    | exact resolve eq227 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq230 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq228
    | exact resolve eq228 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq232 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq230
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq230
    | exact resolve eq230 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq241 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 (σ y)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq258 : (M.op (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq241
       have i₂ := eq190 sF4
       grind)
    | exact superpose eq190 eq241
    | exact resolve eq241 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq261 : (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq258
       have i₂ := eq190 sF3
       grind)
    | exact superpose eq190 eq258
    | exact resolve eq258 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq312 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (M.op x y) (M.op x (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq218 (σ X0)
       grind)
    | exact superpose eq218 eq10
    | exact resolve eq10 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq766 : ∀ X0 X1 X2 X3 : G, (k (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (k X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq191 (M.op X1 X2) X3 (M.op X1 X0)
       have i₂ := eq191 X1 X2 X0
       grind)
    | exact superpose eq191 eq191
    | exact resolve eq191 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : ∀ X0 X1 X2 X3 : G, (k X0 X0) = (M.op (M.op (M.op X1 X2) X3) (k X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq766 X0 X1 X2 X3
       have i₂ := eq202 X1 X0
       grind)
    | exact superpose eq202 eq766
    | exact resolve eq766 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq891 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq895 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq895
       have i₂ := eq190 sF2
       grind)
    | exact superpose eq190 eq895
    | exact resolve eq895 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq969 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq891
       have i₂ := eq190 x
       grind)
    | exact superpose eq190 eq891
    | exact resolve eq891 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq1117 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (k y x) = (M.op y y) := by
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
  have eq1121 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1141 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1121
       have i₂ := eq190 sF2
       grind)
    | exact superpose eq190 eq1121
    | exact resolve eq1121 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1145 : (M.op x y) ≠ (k x x) ∨ (M.op x y) = (M.op y x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq1117
       have i₂ := eq190 x
       grind)
    | exact superpose eq190 eq1117
    | exact resolve eq1117 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1155 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1141
       have i₂ := eq190 sF3
       grind)
    | exact superpose eq190 eq1141
    | exact resolve eq1141 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1159 : (k y x) = (k y y) ∨ (M.op x y) ≠ (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1145
       have i₂ := eq190 y
       grind)
    | exact superpose eq190 eq1145
    | exact resolve eq1145 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1168 : (M.op x y) ≠ (k x x) ∨ (k y x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1159
       have i₂ := eq224
       grind)
    | exact superpose eq224 eq1159
    | exact resolve eq1159 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq1159
  have eq1226 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (k X0 X0)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191 (M.op X0 X1) X2 (k X0 X0)
       have i₂ := eq199 X0 X1
       grind)
    | exact superpose eq199 eq191
    | exact resolve eq191 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq199
  have eq1227 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1226 X0 x x
       have i₂ := eq833 X0 X0 x x
       grind)
    | exact superpose eq833 eq1226
    | exact resolve eq1226 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq1226
  have eq2582 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op x y) (M.op x (σ (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq312 (M.op X1 X0)
       have i₂ := eq202 X1 X0
       grind)
    | exact superpose eq202 eq312
    | exact resolve eq312 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq312
  have eq17199 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq969
       grind)
    | exact superpose eq969 eq39
    | exact resolve eq39 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq17200 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq17199
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17199
    | exact resolve eq17199 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17199
  have eq17202 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq17200
    | exact resolve eq17200 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17200
  have eq165024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq17202 eq965
    | exact resolve eq965 eq17202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165035 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq165024
       have r₂ := eq27
       grind)
    | exact resolve eq165024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165024
  have eq165052 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq165035 eq1155
    | (have r₁ := eq1155
       have r₂ := eq165035
       grind)
    | exact resolve eq1155 eq165035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165076 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq165035 eq1227
    | exact resolve eq1227 eq165035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165035
  have eq165228 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq165052
  have eq165229 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq165228
  have eq165282 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq261 eq165076
    | exact resolve eq165076 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq165076
  have eq165291 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq17202 eq165229
    | exact resolve eq165229 eq17202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165229
  have eq165665 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq165291 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq165291
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq165291
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq165291
       grind)
    | exact resolve eq13 eq165291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165291
  have eq165805 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq165665
       have r₂ := eq26
       grind)
    | exact resolve eq165665 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165665
  have eq165854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq17202 eq165805
    | exact resolve eq165805 eq17202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165805
  have eq165893 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq165854
       have r₂ := eq27
       grind)
    | exact resolve eq165854 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165854
  have eq165943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq165893 eq165282
    | exact resolve eq165282 eq165893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165282 eq165893
  have eq166120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq165943
  have eq166220 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq166120
       have r₂ := eq27
       grind)
    | exact resolve eq166120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166120
  have eq168690 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq166220 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq166220
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq166220
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq166220
       grind)
    | exact resolve eq13 eq166220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166220
  have eq168832 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq168690
       have r₂ := eq26
       grind)
    | exact resolve eq168690 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168690
  have eq168885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq17202 eq168832
    | exact resolve eq168832 eq17202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17202 eq168832
  have eq168929 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq168885
       have r₂ := eq27
       grind)
    | exact resolve eq168885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168885
  have eq168976 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1168
       have i₂ := eq168929
       grind)
    | exact superpose eq168929 eq1168
    | (have r₁ := eq1168
       have r₂ := eq168929
       grind)
    | exact resolve eq1168 eq168929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq168980 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq168929
       grind)
    | exact superpose eq168929 eq39
    | exact resolve eq39 eq168929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169000 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1227 x
       have i₂ := eq168929
       grind)
    | exact superpose eq168929 eq1227
    | exact resolve eq1227 eq168929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq168929
  have eq169151 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq168976
  have eq169152 : (k y x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq169151
  have eq169237 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq168980
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq168980
    | exact resolve eq168980 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168980
  have eq169239 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq169000 eq169152
    | exact resolve eq169152 eq169000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169000 eq169152
  have eq169282 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq169237
    | exact resolve eq169237 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169237
  have eq170109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq169239
       grind)
    | exact superpose eq169239 eq39
    | exact resolve eq39 eq169239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169239
  have eq170115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq170109
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq170109
    | exact resolve eq170109 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170109
  have eq170121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq170115
    | exact resolve eq170115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170115
  have eq171169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq170121 eq965
    | exact resolve eq965 eq170121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171179 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq171169
       have r₂ := eq27
       grind)
    | exact resolve eq171169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171169
  have eq171186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq169282 eq171179
    | exact resolve eq171179 eq169282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169282 eq171179
  have eq171189 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq171186
       have r₂ := eq27
       grind)
    | exact resolve eq171186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171186
  have eq171788 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq171189 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq171189
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq171189
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq171189
       grind)
    | exact resolve eq13 eq171189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171189
  have eq171932 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq171788
       have r₂ := eq26
       grind)
    | exact resolve eq171788 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171788
  have eq171989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq170121 eq171932
    | exact resolve eq171932 eq170121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170121 eq171932
  have eq172038 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq171989
       have r₂ := eq27
       grind)
    | exact resolve eq171989 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171989
  have eq172085 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq172038
       grind)
    | exact superpose eq172038 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq172038
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq172038
       grind)
    | exact resolve eq13 eq172038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172137 : (σ (k x x)) = (M.op (M.op x y) (M.op x (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2582 x y
       have i₂ := eq172038
       grind)
    | exact superpose eq172038 eq2582
    | exact resolve eq2582 eq172038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582 eq172038
  have eq172186 : (σ (k x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq178 eq172137
    | exact resolve eq172137 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq172137
  have eq172226 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq172085
       have r₂ := eq18
       grind)
    | exact resolve eq172085 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq172085
  have eq172252 : (σ (k x x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq172186
       have i₂ := eq190 (σ sF0)
       grind)
    | exact superpose eq190 eq172186
    | exact resolve eq172186 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq172186
  have eq172294 : (σ (k x x)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq172252
       have i₂ := eq10 sF0 sF0
       grind)
    | exact superpose eq10 eq172252
    | exact resolve eq172252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172252
  have eq172316 : (σ (k x x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq172294
    | exact resolve eq172294 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq172294
  have eq172323 : (σ (k x x)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq172316
    | exact resolve eq172316 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172316
  have eq172326 : (σ (k x x)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq232 eq172323
    | exact resolve eq172323 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq172323
  have eq172327 : (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq172326
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq172326
    | exact resolve eq172326 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172326
  have eq172328 : (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq172327
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq172327
    | exact resolve eq172327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq172327
  have eq172332 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq172226
       grind)
    | exact superpose eq172226 eq39
    | exact resolve eq39 eq172226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq172226
  have eq172336 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq172332
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq172332
    | exact resolve eq172332 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq172332
  have eq172341 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq172336
    | exact resolve eq172336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq172336
  have eq172358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq172341 eq965
    | exact resolve eq965 eq172341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq172367 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq172358
       have r₂ := eq27
       grind)
    | exact resolve eq172358 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172358
  have eq176417 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq172367 eq1155
    | (have r₁ := eq1155
       have r₂ := eq172367
       grind)
    | exact resolve eq1155 eq172367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq176598 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq176417
  have eq176599 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq176598
  have eq176661 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq172328 eq176599
    | exact resolve eq176599 eq172328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172328 eq176599
  have eq176692 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq172341 eq176661
    | exact resolve eq176661 eq172341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176661
  have eq176752 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq176692 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq176692
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq176692
       grind)
    | exact resolve eq13 eq176692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176692
  have eq176893 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq176752
       have r₂ := eq26
       grind)
    | exact resolve eq176752 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176752
  have eq176944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq172341 eq176893
    | exact resolve eq176893 eq172341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176893
  have eq176976 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq176944
       have r₂ := eq27
       grind)
    | exact resolve eq176944 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176944
  have eq177003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq176976 eq172367
    | exact resolve eq172367 eq176976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172367 eq176976
  have eq177256 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq177003
       have r₂ := eq27
       grind)
    | exact resolve eq177003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177003
  have eq177822 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq177256 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq177256
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq177256
       grind)
    | exact resolve eq13 eq177256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177256
  have eq177961 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq177822
       have r₂ := eq26
       grind)
    | exact resolve eq177822 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq177822
  have eq178013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172341 eq177961
    | exact resolve eq177961 eq172341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172341 eq177961
  have eq178048 : False := by grind
  exact eq178048

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxx_pyx_pxy_Equation3698 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq19 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : (M.op x y) = (M.op x y) := by grind
  have eq25 : (M.op x y) = (M.op x y) := by grind
  clear eq24
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq27 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq26
  have eq28 : (σ x) = (σ x) := by grind
  have eq29 : (σ x) = (σ x) := by grind
  clear eq28
  have eq30 : (σ y) = (σ y) := by grind
  have eq31 : (σ y) = (σ y) := by grind
  clear eq30
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq33 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq32
  have eq34 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq19
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq36 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq23 eq22
    | (have j1 := eq23 X0
       grind)
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq42 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq25
    | exact resolve eq25 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39
  have eq43 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq41
       grind)
    | exact superpose eq41 eq42
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq48 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (τ X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq47
    | exact resolve eq47 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X2 X3) (M.op X2 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op (τ (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq33 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op X3 X2) ∨ (M.op X3 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq90 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : ∀ X0 X1 X2 X3 : G, (k X3 X2) = (k X3 X3) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X0 X1 X2 X3
       have i₂ := eq94 X3
       grind)
    | exact superpose eq94 eq92
    | (have j0 := eq92 X0 X1 X2 X3
       grind)
    | exact resolve eq92 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq100 : ∀ X2 X3 : G, (M.op X3 X2) ≠ (k X2 X2) ∨ (k X3 X2) = (k X3 X3) := by
    intro X2 X3
    first
    | (have i₁ := eq97 x x X2 X3
       have i₂ := eq95 x x X2
       grind)
    | exact superpose eq95 eq97
    | (have j0 := eq97 x x X2 X3
       grind)
    | exact resolve eq97 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq119 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq43 eq14
    | (have j0 := eq14 (M.op x y) (k (τ (σ x)) (τ (σ y)))
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq33 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq94 sF5
       grind)
    | exact superpose eq94 eq121
    | exact resolve eq121 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq139 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq94 (τ sF5)
       grind)
    | exact superpose eq94 eq119
    | exact resolve eq119 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq168 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq48
    | exact resolve eq48 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq227 : ∀ X0 : G, (M.op (M.op x y) (M.op (τ (σ x)) X0)) ≠ (M.op (M.op x y) (M.op (τ (σ x)) X0)) ∨ (M.op (M.op x y) (M.op (τ (σ x)) X0)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq12
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq234 : ∀ X0 : G, (M.op (M.op x y) (M.op (τ (σ x)) X0)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq227 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq258 : (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq69 sF4
       have i₂ := eq94 sF4
       grind)
    | exact superpose eq94 eq69
    | exact resolve eq69 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq320 : (k (τ (σ y)) (τ (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq43 eq234
    | exact resolve eq234 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq333 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq320
       have i₂ := eq94 sF2
       grind)
    | exact superpose eq94 eq320
    | exact resolve eq320 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq362 : (σ (k (M.op x y) (M.op x y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) := by
    first
    | exact superpose eq333 eq15
    | exact resolve eq15 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : (σ (k (M.op x y) (M.op x y))) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq362
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq362
    | exact resolve eq362 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq365 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq363
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq363
    | exact resolve eq363 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq366 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq365
    | exact resolve eq365 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq385 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (M.op (k X0 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95 (M.op X1 X2) (M.op X1 X0) X3
       have i₂ := eq95 X1 X2 X0
       grind)
    | exact superpose eq95 eq95
    | exact resolve eq95 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 : G, (M.op (M.op (τ (σ x)) X0) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq43 eq95
    | exact resolve eq95 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq33 eq95
    | (have j0 := eq95 (σ x) X0 (σ y)
       grind)
    | exact resolve eq95 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 : G, (M.op (M.op (τ (σ x)) X0) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq333 eq402
    | exact resolve eq402 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq469 : ∀ X0 : G, (k (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op (τ (σ x)) X0) (M.op (τ (σ x)) X0)) = (k (M.op (τ (σ x)) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq438 eq12
    | (have j0 := eq12 (M.op (τ (σ x)) X0) (M.op x y)
       grind)
    | exact resolve eq12 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq474 : ∀ X0 : G, (M.op (M.op (τ (σ x)) X0) (M.op (τ (σ x)) X0)) = (k (M.op (τ (σ x)) X0) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq469 X0
       grind)
    | (have r₁ := eq469 X0
       have r₂ := eq94 (M.op x y)
       grind)
    | exact resolve eq469 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq477 : ∀ X0 : G, (k X0 X0) = (k (M.op (τ (σ x)) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq474 x
       have i₂ := eq95 (τ sF4) x x
       grind)
    | exact superpose eq95 eq474
    | exact resolve eq474 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq480 : (k (τ (σ x)) (τ (σ x))) = (k (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by
    first
    | (have i₁ := eq477 (τ sF4)
       have i₂ := eq94 (τ sF4)
       grind)
    | exact superpose eq94 eq477
    | exact resolve eq477 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq633 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X3 X4)) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) (M.op (M.op X3 X4) (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq66 (M.op X3 X4) (M.op X3 X4) X3 X4
       have i₂ := eq66 X0 (M.op (M.op X3 X4) (M.op X3 X4)) X1 X2
       grind)
    | exact superpose eq66 eq66
    | exact resolve eq66 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq696 : ∀ X0 X1 X2 X4 : G, (k X4 X4) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) (k X4 X4))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq633 X0 X1 X2 X0 X2
       have i₂ := eq95 X0 X2 X2
       grind)
    | exact superpose eq95 eq633
    | exact resolve eq633 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq633
  have eq754 : ∀ X0 X1 X2 X4 : G, (k X4 X4) = (M.op (k X0 X0) (M.op (M.op X1 X2) (k X4 X4))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq696 X0 X1 X2 X4
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq696
    | exact resolve eq696 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq793 : ∀ X4 : G, (k X4 X4) = (k (k X4 X4) (k X4 X4)) := by
    intro X4
    first
    | (have i₁ := eq754 x x x X4
       have i₂ := eq385 x x x (k X4 X4)
       grind)
    | exact superpose eq385 eq754
    | exact resolve eq754 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq754
  have eq1264 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq137 eq34
    | exact resolve eq34 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq43 eq100
    | (have j0 := eq100 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq100 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1326 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq33 eq100
    | (have j0 := eq100 (σ y) (σ x)
       grind)
    | exact resolve eq100 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1334 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq333 eq1320
    | exact resolve eq1320 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq1320
  have eq7886 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq137 eq1326
    | (have r₁ := eq1326
       have r₂ := eq137
       grind)
    | exact resolve eq1326 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq1326
  have eq7887 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7886
  have eq34617 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq139 eq793
    | exact resolve eq793 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34656 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq139 eq15
    | exact resolve eq15 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq34659 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq34656
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq34656
    | exact resolve eq34656 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34656
  have eq34666 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq27 eq34659
    | exact resolve eq34659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34659
  have eq34752 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq34617 eq15
    | exact resolve eq15 eq34617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34617
  have eq34824 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq34752
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq34752
    | exact resolve eq34752 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34752
  have eq34825 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq34824
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq34824
    | exact resolve eq34824 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34824
  have eq34826 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq27 eq34825
    | exact resolve eq34825 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34825
  have eq57376 : (k (τ (σ x)) (τ (σ y))) = (τ (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7887 eq168
    | exact resolve eq168 eq7887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7887
  have eq57468 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57376
       have i₂ := eq168 sF4 sF4
       grind)
    | exact superpose eq168 eq57376
    | exact resolve eq57376 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq57376
  have eq285671 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq57468 eq34666
    | exact resolve eq34666 eq57468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34666 eq57468
  have eq285795 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq285671
       have r₂ := eq1264
       grind)
    | exact resolve eq285671 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285671
  have eq527645 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq285795 eq793
    | exact resolve eq793 eq285795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq285795
  have eq528881 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq527645 eq34
    | exact resolve eq34 eq527645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527645
  have eq529037 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq528881
       have r₂ := eq34826
       grind)
    | exact resolve eq528881 eq34826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34826 eq528881
  have eq529048 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq529037 eq1334
    | (have r₁ := eq1334
       have r₂ := eq529037
       grind)
    | exact resolve eq1334 eq529037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq529514 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq529037 eq15
    | exact resolve eq15 eq529037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529037
  have eq529526 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq529048
  have eq529527 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq529514
    | exact resolve eq529514 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529514
  have eq529560 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq366 eq529527
    | exact resolve eq529527 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529527
  have eq530674 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq529560 eq1264
    | (have r₁ := eq1264
       have r₂ := eq529560
       grind)
    | exact resolve eq1264 eq529560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq530844 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq530674
  have eq530845 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq530844
  have eq530955 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq530845 eq34
    | exact resolve eq34 eq530845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530968 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op (σ x) X0) (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq530845 eq406
    | exact resolve eq406 eq530845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq530845
  have eq532207 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq529560 eq530955
    | exact resolve eq530955 eq529560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529560 eq530955
  have eq532216 : (k (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq532207
  have eq774884 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq529526 eq15
    | exact resolve eq15 eq529526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529526
  have eq774895 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ x))) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq774884
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq774884
    | exact resolve eq774884 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774884
  have eq774896 : (k (σ x) (σ y)) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq774895
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq774895
    | exact resolve eq774895 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774895
  have eq774897 : (k (σ x) (σ y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq774896
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq774896
    | exact resolve eq774896 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774896
  have eq774898 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq774897
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq774897
    | exact resolve eq774897 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774897
  have eq853681 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq33 eq530968
    | (have j0 := eq530968 (σ y)
       grind)
    | exact resolve eq530968 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530968
  have eq853816 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq774898 eq853681
    | exact resolve eq853681 eq774898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853681
  have eq853927 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq853816
  have eq853984 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq258 eq853927
    | exact resolve eq853927 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq853927
  have eq855396 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq853984 eq532216
    | exact resolve eq532216 eq853984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532216 eq853984
  have eq855595 : (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq855396
  have eq855610 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq855595
       have r₂ := eq774898
       grind)
    | exact resolve eq855595 eq774898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774898 eq855595
  have eq855683 : (σ y) = (σ (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq855610 eq36
    | exact resolve eq36 eq855610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855610
  have eq855745 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq855683
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq855683
    | exact resolve eq855683 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq855683
  have eq855746 : (σ x) = (σ y) := by grind
  clear eq855745
  have eq857180 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq855746 eq33
    | exact resolve eq33 eq855746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq857181 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq855746 eq43
    | exact resolve eq43 eq855746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq857545 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq857181
       have i₂ := eq94 (τ sF4)
       grind)
    | exact superpose eq94 eq857181
    | exact resolve eq857181 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857181
  have eq857546 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq857180
       have i₂ := eq94 sF4
       grind)
    | exact superpose eq94 eq857180
    | exact resolve eq857180 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq857180
  have eq857552 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq857546 eq34
    | exact resolve eq34 eq857546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq857546
  have eq860536 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq857545 eq480
    | exact resolve eq480 eq857545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq857545
  have eq863417 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq860536 eq15
    | exact resolve eq15 eq860536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860536
  have eq863420 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq863417
    | exact resolve eq863417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq863417
  have eq863611 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq366 eq863420
    | exact resolve eq863420 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq863420
  have eq863667 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq855746 eq863611
    | exact resolve eq863611 eq855746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855746 eq863611
  have eq863703 : False := by grind
  exact eq863703

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq50 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq50 (σ X0)
       grind)
    | exact superpose eq50 eq15
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq64
    | exact resolve eq64 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq64
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq88
    | (have j0 := eq88 (σ X0) (σ X1)
       grind)
    | exact resolve eq88 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq10
    | (have j1 := eq89 X0 X1
       grind)
    | exact resolve eq10 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq719 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq697
    | (have j0 := eq697 X0 X1
       grind)
    | exact resolve eq697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq756 : x = y ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq719 y x
       grind)
    | exact superpose eq719 eq16
    | (have j1 := eq719 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq719 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq719 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq784 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq756
       grind)
    | exact superpose eq756 eq16
    | exact resolve eq16 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq785 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have r₁ := eq784
       have r₂ := eq73 x
       grind)
    | exact resolve eq784 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq785
       have i₂ := eq88 y x
       grind)
    | exact superpose eq88 eq785
    | (have j1 := eq88 x y
       grind)
    | (have r₁ := eq785
       have r₂ := eq88 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq785
       have r₂ := eq88 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq785 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq785
  have eq934 : x = y := by grind
  clear eq931
  have eq937 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq934
       grind)
    | exact superpose eq934 eq16
    | exact resolve eq16 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq938 : False := by grind
  exact eq938

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq33 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq33 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq33 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq59 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq60 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq60 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq60 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq64
    | (have j0 := eq64 X0 X1
       grind)
    | exact resolve eq64 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq64
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq70 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | exact resolve eq70 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq70
  have eq728 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq78 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq735 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq728 X0 X1
       have j1 := eq75 X1 X0
       grind)
    | (have r₁ := eq728 X1 X1
       have r₂ := eq75 X1 X1
       grind)
    | (have r₁ := eq728 X1 X0
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq728 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq728
  have eq2125 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq735 (σ X1) (σ X0)
       grind)
    | exact superpose eq735 eq15
    | exact resolve eq15 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2128 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2125 X0 X1
       have i₂ := eq735 X1 X0
       grind)
    | exact superpose eq735 eq2125
    | exact resolve eq2125 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq2125
  have eq2132 : False := by grind
  exact eq2132

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation3868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3868 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
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
  have eq64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq92 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq77 (σ X0)
       grind)
    | exact superpose eq77 eq15
    | exact resolve eq15 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq92
    | exact resolve eq92 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq92
  have eq121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq103
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq103 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       have j1 := eq121 X0 X1
       grind)
    | (have r₁ := eq141 X0 X1
       have r₂ := eq121 X0 X1
       grind)
    | (have r₁ := eq141 X0 (σ (M.op X0 X0))
       have r₂ := eq121 X0 X1
       grind)
    | (have r₁ := eq141 (M.op X0 X0) (σ X0)
       have r₂ := eq121 X0 X1
       grind)
    | exact resolve eq141 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq141
  have eq170 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq148
    | exact resolve eq148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq148 X1 (σ X0)
       grind)
    | exact superpose eq148 eq15
    | (have j1 := eq148 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq182 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq170 (τ X1) X0
       grind)
    | exact superpose eq170 eq19
    | (have j1 := eq170 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq170
  have eq270 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq295 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq270
    | (have j0 := eq270 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq930 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175 x y
       grind)
    | exact superpose eq175 eq16
    | (have j1 := eq175 x y
       grind)
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq947 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq930
       have i₂ := eq295 y x
       grind)
    | exact superpose eq295 eq930
    | (have j1 := eq295 (σ x) (σ y)
       grind)
    | (have r₁ := eq930
       have r₂ := eq295 y x
       grind)
    | (have r₁ := eq930
       have r₂ := eq295 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq930
       have r₂ := eq295 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq930 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq930
  have eq948 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq947
  have eq950 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq16
    | exact resolve eq16 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq951 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq950
       have r₂ := eq103 x
       grind)
    | exact resolve eq950 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq952 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq951
       grind)
    | exact superpose eq951 eq16
    | exact resolve eq16 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq951
       grind)
    | exact superpose eq951 eq10
    | exact resolve eq10 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq995 : x = y := by
    first
    | (have i₁ := eq953
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq953
    | exact resolve eq953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq996 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq952
       have i₂ := eq103 x
       grind)
    | exact superpose eq103 eq952
    | exact resolve eq952 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq952
  have eq997 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq996
       have i₂ := eq995
       grind)
    | exact superpose eq995 eq996
    | exact resolve eq996 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq996
  have eq998 : False := by grind
  exact eq998

/-- `Equation3873`: `x ◇ x = (x ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pxx_y_pyx_Equation3873 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3873 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3873.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq705 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq5372 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq705 x y
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq705
    | (have j0 := eq705 x y
       grind)
    | exact resolve eq705 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5416 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5372
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5372
    | exact resolve eq5372 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5372
  have eq5504 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5416
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5416
    | exact resolve eq5416 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5416
  have eq5592 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5504
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5504
    | exact resolve eq5504 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504
  have eq5676 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq5592
    | exact resolve eq5592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5592
  have eq5758 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5676
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5676
    | exact resolve eq5676 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5676
  have eq5828 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5758
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5758
    | exact resolve eq5758 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758
  have eq14214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14221 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq14214
    | exact resolve eq14214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14214
  have eq14232 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq14221
       have r₂ := eq27
       grind)
    | exact resolve eq14221 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14221
  have eq14234 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq14232
    | exact resolve eq14232 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14232
  have eq14237 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14234 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14234
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14234
       grind)
    | exact resolve eq13 eq14234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14238 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq14234 eq14
    | exact resolve eq14 eq14234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14275 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq14237
  have eq14415 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14275 eq115
    | exact resolve eq115 eq14275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14275
  have eq14429 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14415
  have eq15227 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14234 eq14238
    | exact resolve eq14238 eq14234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14234 eq14238
  have eq15289 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq15227
  have eq15290 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq15289
    | exact resolve eq15289 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15289
  have eq15300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15290 eq14429
    | exact resolve eq14429 eq15290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14429 eq15290
  have eq15342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15300
  have eq15356 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15342
       have r₂ := eq27
       grind)
    | exact resolve eq15342 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15342
  have eq15362 : x ≠ x ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15356
       grind)
    | exact superpose eq15356 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15356
       grind)
    | exact resolve eq13 eq15356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15363 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq15356
       grind)
    | exact superpose eq15356 eq14
    | exact resolve eq14 eq15356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15400 : (k y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15362
  have eq15405 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15400
       grind)
    | exact superpose eq15400 eq72
    | exact resolve eq72 eq15400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15400
  have eq15518 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15363 y
       have i₂ := eq15356
       grind)
    | exact superpose eq15356 eq15363
    | exact resolve eq15363 eq15356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15356 eq15363
  have eq15582 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15518
  have eq15584 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15582
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15582
    | exact resolve eq15582 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15582
  have eq15586 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15405
       have i₂ := eq15584
       grind)
    | exact superpose eq15584 eq15405
    | exact resolve eq15405 eq15584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15405 eq15584
  have eq15629 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15586
  have eq15643 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15629
    | exact resolve eq15629 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15629
  have eq15659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15643 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq15643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15659
    | exact resolve eq15659 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15659
  have eq15679 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15668
       have r₂ := eq27
       grind)
    | exact resolve eq15668 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15668
  have eq15681 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15679
    | exact resolve eq15679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15679
  have eq15682 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15681
  have eq15768 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15682 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15682
       grind)
    | exact resolve eq13 eq15682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15769 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15682 eq14
    | exact resolve eq14 eq15682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15806 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15768
  have eq15822 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15806 eq15643
    | exact resolve eq15643 eq15806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15643 eq15806
  have eq15830 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15822
  have eq16471 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15682 eq15769
    | exact resolve eq15769 eq15682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15682 eq15769
  have eq16537 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16471
  have eq16539 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16537
    | exact resolve eq16537 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16537
  have eq16551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16539 eq15830
    | exact resolve eq15830 eq16539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15830 eq16539
  have eq16593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16551
  have eq16609 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16593
       have r₂ := eq27
       grind)
    | exact resolve eq16593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16593
  have eq16614 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16609 eq27
    | exact resolve eq27 eq16609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16615 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16609 eq51
    | exact resolve eq51 eq16609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq16617 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16609 eq76
    | (have r₁ := eq76
       have r₂ := eq16609
       grind)
    | exact resolve eq76 eq16609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq16609
  have eq16625 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq16617
  have eq16765 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16625 eq82
    | exact resolve eq82 eq16625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq16766 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16625 eq115
    | exact resolve eq115 eq16625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16800 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq16766
  have eq16814 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16800
       have r₂ := eq16614
       grind)
    | exact resolve eq16800 eq16614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16800
  have eq16815 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq16765
    | exact resolve eq16765 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16765
  have eq16820 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16814 eq16615
    | exact resolve eq16615 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16824 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16814 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16814
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16814
       grind)
    | exact resolve eq13 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16814
  have eq16862 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq16824
  have eq16865 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq16820
  have eq16867 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq16865
    | exact resolve eq16865 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16865
  have eq16868 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16815 eq16615
    | exact resolve eq16615 eq16815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16815
  have eq16913 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq16868
  have eq16915 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq26 eq16913
    | exact resolve eq16913 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16913
  have eq18064 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16862 eq115
    | exact resolve eq115 eq16862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq16862
  have eq18094 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq18064
  have eq18119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq18094 eq16867
    | exact resolve eq16867 eq18094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16867
  have eq18120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq18094 eq16915
    | exact resolve eq16915 eq18094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16915 eq18094
  have eq18164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq18120
  have eq18165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq18119
  have eq18173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq18164
       have r₂ := eq75
       grind)
    | exact resolve eq18164 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq18164
  have eq18174 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18165
       have r₂ := eq27
       grind)
    | exact resolve eq18165 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18165
  have eq18184 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq18173
       have r₂ := eq27
       grind)
    | exact resolve eq18173 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18173
  have eq18188 : x ≠ x ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18174
       grind)
    | exact superpose eq18174 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18174
       grind)
    | exact resolve eq13 eq18174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18189 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18174
       grind)
    | exact superpose eq18174 eq14
    | exact resolve eq14 eq18174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18226 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq18188
  have eq18374 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq18184
       grind)
    | exact superpose eq18184 eq72
    | exact resolve eq72 eq18184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18184
  have eq18420 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18374
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18374
    | exact resolve eq18374 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18374
  have eq18462 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq18226
       grind)
    | exact superpose eq18226 eq72
    | exact resolve eq72 eq18226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18226
  have eq18772 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18189 y
       have i₂ := eq18174
       grind)
    | exact superpose eq18174 eq18189
    | exact resolve eq18189 eq18174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18174 eq18189
  have eq18842 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq18772
  have eq18846 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18842
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18842
    | exact resolve eq18842 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18842
  have eq18996 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18462
       have i₂ := eq18846
       grind)
    | exact superpose eq18846 eq18462
    | exact resolve eq18462 eq18846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18462 eq18846
  have eq19041 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18996
  have eq19054 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq19041
    | exact resolve eq19041 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19041
  have eq19077 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19054 eq16625
    | exact resolve eq16625 eq19054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16625
  have eq19088 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19077
  have eq19098 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19088
       have r₂ := eq16614
       grind)
    | exact resolve eq19088 eq16614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16614 eq19088
  have eq19115 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19098 eq16615
    | exact resolve eq16615 eq19098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16615
  have eq19119 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19098 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19098
       grind)
    | exact resolve eq13 eq19098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19098
  have eq19157 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19119
  have eq19160 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19115
  have eq19162 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19160
    | exact resolve eq19160 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19160
  have eq19552 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19157 eq19054
    | exact resolve eq19054 eq19157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19054 eq19157
  have eq19560 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19552
  have eq19597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19560 eq19162
    | exact resolve eq19162 eq19560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19162 eq19560
  have eq19641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19597
  have eq19652 : x = (M.op x y) := by
    first
    | (have r₁ := eq19641
       have r₂ := eq27
       grind)
    | exact resolve eq19641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19641
  have eq19802 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19652 eq20
    | exact resolve eq20 eq19652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq19804 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 x) X0) := by
    intro X0
    first
    | exact superpose eq19652 eq50
    | exact resolve eq50 eq19652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq19924 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19802
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19802
    | exact resolve eq19802 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19802
  have eq19961 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19924 eq26
    | exact resolve eq26 eq19924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20042 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19924 eq18420
    | exact resolve eq18420 eq19924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18420
  have eq20466 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | exact superpose eq19924 eq5828
    | exact resolve eq5828 eq19924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5828
  have eq20467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | exact superpose eq19924 eq20466
    | exact resolve eq20466 eq19924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20466
  have eq20468 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq20467
       have r₂ := eq27
       grind)
    | exact resolve eq20467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20467
  have eq20469 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq19924 eq20468
    | exact resolve eq20468 eq19924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20468
  have eq20595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20042 eq20469
    | (have r₁ := eq20469
       have r₂ := eq20042
       grind)
    | exact resolve eq20469 eq20042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20469
  have eq20605 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by grind
  clear eq20595
  have eq20640 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20605 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq20605
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20605
       grind)
    | exact resolve eq13 eq20605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20641 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ (M.op x y))) X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20605 eq14
    | exact resolve eq14 eq20605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20678 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq20640
  have eq23499 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20678 eq20042
    | exact resolve eq20042 eq20678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20042 eq20678
  have eq23508 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq23499
  have eq31033 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20605 eq20641
    | exact resolve eq20641 eq20605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20605 eq20641
  have eq31102 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq31033
  have eq31107 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19961 eq31102
    | exact resolve eq31102 eq19961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31102
  have eq31128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31107 eq23508
    | exact resolve eq23508 eq31107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23508 eq31107
  have eq31170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq31128
  have eq31191 : x = (M.op y x) := by
    first
    | (have r₁ := eq31170
       have r₂ := eq27
       grind)
    | exact resolve eq31170 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31170
  have eq31212 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq19804 y
       have i₂ := eq31191
       grind)
    | exact superpose eq31191 eq19804
    | exact resolve eq19804 eq31191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19804
  have eq31216 : x ≠ x ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq31191
       grind)
    | exact superpose eq31191 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq31191
       grind)
    | exact resolve eq13 eq31191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31191
  have eq31254 : (k y x) = (M.op y y) := by grind
  clear eq31216
  have eq31257 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq31212
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31212
    | exact resolve eq31212 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq31212
  have eq31259 : x = (M.op y y) := by
    first
    | exact superpose eq19652 eq31257
    | exact resolve eq31257 eq19652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19652 eq31257
  have eq31322 : x = (k y x) := by
    first
    | (have i₁ := eq31254
       have i₂ := eq31259
       grind)
    | exact superpose eq31259 eq31254
    | exact resolve eq31254 eq31259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31254 eq31259
  have eq31331 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq31322
       grind)
    | exact superpose eq31322 eq72
    | exact resolve eq72 eq31322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq31359 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq705 x y
       have i₂ := eq31322
       grind)
    | exact superpose eq31322 eq705
    | (have j0 := eq705 x y
       grind)
    | exact resolve eq705 eq31322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq31322
  have eq31364 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq31359
  have eq31377 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq31364
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31364
    | exact resolve eq31364 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31364
  have eq31388 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq19924 eq31331
    | exact resolve eq31331 eq19924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31331
  have eq31393 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq31377
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31377
    | exact resolve eq31377 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31377
  have eq31403 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq31388
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31388
    | exact resolve eq31388 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31388
  have eq31408 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq31393
    | exact resolve eq31393 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31393
  have eq31418 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq19924 eq31403
    | exact resolve eq31403 eq19924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31403
  have eq31423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq19924 eq31408
    | exact resolve eq31408 eq19924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31408
  have eq31432 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq31423
       have r₂ := eq27
       grind)
    | exact resolve eq31423 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31423
  have eq31438 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq31432
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31432
    | exact resolve eq31432 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31432
  have eq31444 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq19924 eq31438
    | exact resolve eq31438 eq19924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19924 eq31438
  have eq31450 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq31444
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31444
    | exact resolve eq31444 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31444
  have eq31565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq31450 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq31450
       grind)
    | exact resolve eq13 eq31450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31566 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq31450 eq14
    | exact resolve eq14 eq31450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31603 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by grind
  clear eq31565
  have eq31607 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq31418 eq31603
    | exact resolve eq31603 eq31418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31418 eq31603
  have eq32032 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq31450 eq31566
    | exact resolve eq31566 eq31450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31450 eq31566
  have eq32104 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19961 eq32032
    | exact resolve eq32032 eq19961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19961 eq32032
  have eq32107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31607 eq32104
    | exact resolve eq32104 eq31607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31607 eq32104
  have eq32108 : False := by grind
  exact eq32108
