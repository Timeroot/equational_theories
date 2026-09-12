import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_x_pyx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
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
  have eq28 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) = X1 ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X0 X2) = X2 := by
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) = X1 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq28 X0 X1 X2
       have r₂ := eq12 (M.op (M.op X0 X0) X0) X1
       grind)
    | (have r₁ := eq28 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq100 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq20 (M.op X0 X0) x x X3
       have i₂ := eq19 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq19 eq20
    | exact resolve eq20 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq133 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op X1 X1) X1) X0) = (M.op X0 (M.op (M.op X1 X1) X1)) ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X1) X1) X0
       have i₂ := eq33 X1 X0 X2
       grind)
    | exact superpose eq33 eq12
    | (have j0 := eq12 (M.op (M.op X1 X1) X1) X0
       have j1 := eq33 (M.op (M.op X1 X1) X1) X1 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) X0) X1
       have r₂ := eq33 X0 X1 X2
       grind)
    | exact resolve eq12 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq146 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 X1) X1) X0) = (M.op X0 (M.op (M.op X1 X1) X1)) ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq133 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq155 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 X0 x X2
       have i₂ := eq100 x x
       grind)
    | (have i₁ := eq146 X0 X1 X2
       have i₂ := eq100 X0 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq100 eq146
    | (have j0 := eq146 X0 X1 X0
       grind)
    | exact resolve eq146 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq146
  have eq592 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq155 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq593 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq592 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1452 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq593 (σ X1) (σ X0)
       grind)
    | exact superpose eq593 eq15
    | exact resolve eq15 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1465 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1452 X0 X1
       have i₂ := eq593 X1 X0
       grind)
    | exact superpose eq593 eq1452
    | exact resolve eq1452 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq1452
  have eq1477 : False := by grind
  exact eq1477

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_pyx_pxy_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq77 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq78 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  clear eq44
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq115 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | (have j0 := eq115 y x
       grind)
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq115
    | (have r₁ := eq115 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq115 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq126 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq150 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq115
    | (have r₁ := eq115 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq50 X0
       grind)
    | exact resolve eq115 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq219 : ∀ X0 : G, (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq220 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq115
    | (have r₁ := eq115 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       have r₂ := eq51 X0
       grind)
    | exact resolve eq115 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq225 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq342 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq468 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq127 (τ X0) X1 X2
       grind)
    | exact superpose eq127 eq34
    | exact resolve eq34 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq469 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq468 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq468
    | exact resolve eq468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq576 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)))) := by
    intro X0
    first
    | exact superpose eq225 eq342
    | exact resolve eq342 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq577 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq342 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq127 (σ X0) X1 X2
       grind)
    | exact superpose eq127 eq342
    | exact resolve eq342 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq577 X0 X1 X2
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq577
    | exact resolve eq577 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq603 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq576 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq576
    | exact resolve eq576 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq671 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op X0 X0) x x X3
       have i₂ := eq52 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq703 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq115 x (M.op X0 X0)
       have i₂ := eq671 X0 x
       grind)
    | exact superpose eq671 eq115
    | (have r₁ := eq115 x (M.op X0 X0)
       have r₂ := eq671 X0 x
       grind)
    | exact resolve eq115 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq703 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq730 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 (M.op X1 X1)
       have i₂ := eq713 (σ X0) X1
       grind)
    | exact superpose eq713 eq342
    | exact resolve eq342 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq713
  have eq731 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq730 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq730
    | exact resolve eq730 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq748 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X1) X0))) = (k (M.op X0 (M.op (M.op X1 X1) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       have i₂ := eq52 X0 X1 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq52 eq66
    | exact resolve eq66 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq765 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq748 x X0 X2
       have i₂ := eq671 X0 x
       grind)
    | (have i₁ := eq748 X0 x X2
       have i₂ := eq671 X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq671 eq748
    | exact resolve eq748 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq876 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq890 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq899 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq876 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq876 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq876 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq876 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq908 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq899 X0 X1
       have j1 := eq115 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq899 X0 X1
       have r₂ := eq115 (σ X0) (σ X1)
       grind)
    | exact resolve eq899 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq915 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq908 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq908
    | (have j0 := eq908 X0 X1
       grind)
    | exact resolve eq908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq8442 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq77 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq77
    | (have j0 := eq77 x
       grind)
    | exact resolve eq77 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq8458 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8442
  have eq8464 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8458
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq8458
    | exact resolve eq8458 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq8458
  have eq8481 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq8464
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq8464 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8464
  have eq8486 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq8481 eq49
    | exact resolve eq49 eq8481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq8481
  have eq8618 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq78
    | (have j0 := eq78 y
       grind)
    | exact resolve eq78 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq8633 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq8618
  have eq8638 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8633
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq8633
    | exact resolve eq8633 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq8633
  have eq8662 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq8638
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq8638 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638
  have eq8708 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq8662 eq107
    | exact resolve eq107 eq8662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq8789 : ∀ X0 : G, (k X0 (k x x)) = X0 := by
    intro X0
    first
    | exact superpose eq8486 eq731
    | exact resolve eq731 eq8486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8486
  have eq8861 : ∀ X0 : G, (M.op X0 X0) = (M.op (k x x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8789 (M.op X0 X0)
       have i₂ := eq765 X0 (k x x)
       grind)
    | exact superpose eq765 eq8789
    | exact resolve eq8789 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8789
  have eq8932 : ∀ X0 : G, (k X0 (k y y)) = X0 := by
    intro X0
    first
    | exact superpose eq8708 eq731
    | exact resolve eq731 eq8708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq8708
  have eq9245 : ∀ X0 : G, (M.op X0 X0) = (M.op (k y y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8932 (M.op X0 X0)
       have i₂ := eq765 X0 (k y y)
       grind)
    | exact superpose eq765 eq8932
    | exact resolve eq8932 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8932
  have eq9425 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq150 eq13
    | (have j0 := eq13 (σ X0) (σ x)
       have j1 := eq150 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ X0)
       have r₂ := eq150 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ x)
       have r₂ := eq150 X0
       grind)
    | exact resolve eq13 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq9441 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9425 X0
       have j1 := eq13 (σ X0) (σ x)
       grind)
    | (have r₁ := eq9425 X0
       have r₂ := eq13 (σ x) (σ X0)
       grind)
    | (have r₁ := eq9425 X0
       have r₂ := eq13 (σ X0) (σ x)
       grind)
    | exact resolve eq9425 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9425
  have eq9478 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9441 X0
       have j1 := eq115 (σ X0) (σ x)
       grind)
    | (have r₁ := eq9441 X0
       have r₂ := eq115 (σ X0) (σ x)
       grind)
    | exact resolve eq9441 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9441
  have eq9504 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) ≠ (σ (k X0 x)) := by
    intro X0
    first
    | exact superpose eq39 eq9478
    | (have j0 := eq9478 X0
       grind)
    | exact resolve eq9478 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq9478
  have eq11305 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (k x x)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (k x x)
       have i₂ := eq8861 X0
       grind)
    | exact superpose eq8861 eq14
    | exact resolve eq14 eq8861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8861
  have eq11331 : ∀ X1 : G, (M.op (k x x) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq11305 x X1
       have i₂ := eq671 (M.op x x) (k x x)
       grind)
    | (have i₁ := eq11305 x X1
       have i₂ := eq671 x (M.op (M.op (M.op x x) (M.op x x)) (k x x))
       grind)
    | exact superpose eq671 eq11305
    | exact resolve eq11305 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11305
  have eq11507 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (k y y))) = (k (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (k y y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (M.op X0 X0) (k y y)
       have i₂ := eq9245 X0
       grind)
    | exact superpose eq9245 eq66
    | exact resolve eq66 eq9245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq9245
  have eq11527 : ∀ X1 : G, (M.op X1 (k y y)) = (k (k y y) X1) := by
    intro X1
    first
    | (have i₁ := eq11507 x X1
       have i₂ := eq671 (M.op x x) (k y y)
       grind)
    | (have i₁ := eq11507 x X1
       have i₂ := eq671 x (M.op (M.op (M.op x x) (M.op x x)) (k y y))
       grind)
    | exact superpose eq671 eq11507
    | exact resolve eq11507 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11507
  have eq25566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq25566
    | exact resolve eq25566 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25566
  have eq25584 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq25573
       have r₂ := eq27
       grind)
    | exact resolve eq25573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25573
  have eq25586 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq25584
    | exact resolve eq25584 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25584
  have eq25593 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25586 eq115
    | (have r₁ := eq115 (σ x) (σ y)
       have r₂ := eq25586
       grind)
    | (have r₁ := eq115 (σ y) (σ x)
       have r₂ := eq25586
       grind)
    | (have r₁ := eq115 y x
       have r₂ := eq25586
       grind)
    | exact resolve eq115 eq25586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq25594 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ x)) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq25586 eq127
    | exact resolve eq127 eq25586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq25597 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ x)) (σ y)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq25586 eq602
    | exact resolve eq602 eq25586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq25586
  have eq25605 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq25593
  have eq25614 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq25597 X0
       have i₂ := eq671 sF2 sF3
       grind)
    | (have i₁ := eq25597 X0
       have i₂ := eq671 X0 (M.op (M.op sF2 sF2) sF3)
       grind)
    | exact superpose eq671 eq25597
    | exact resolve eq25597 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25597
  have eq25617 : ∀ X0 : G, x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq25594 X0
       have i₂ := eq671 sF2 sF3
       grind)
    | (have i₁ := eq25594 X0
       have i₂ := eq671 X0 (M.op (M.op sF2 sF2) sF3)
       grind)
    | exact superpose eq671 eq25594
    | exact resolve eq25594 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25594
  have eq25623 : ∀ X0 : G, x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq25614
    | exact resolve eq25614 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25614
  have eq26142 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25605 eq94
    | exact resolve eq94 eq25605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq25605
  have eq26158 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26142
  have eq26172 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq26158
       grind)
    | exact superpose eq26158 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq26158
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq26158
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq26158
       grind)
    | exact resolve eq13 eq26158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26158
  have eq26190 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26172
  have eq26207 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26190
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26190
    | exact resolve eq26190 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26190
  have eq26211 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq26207
       have r₂ := eq124
       grind)
    | exact resolve eq26207 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26207
  have eq26214 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq26211
       grind)
    | exact superpose eq26211 eq73
    | exact resolve eq73 eq26211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq26211
  have eq26242 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq26214
    | exact resolve eq26214 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26214
  have eq29334 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op x x) y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 x y
       have i₂ := eq25617 X1
       grind)
    | exact superpose eq25617 eq469
    | (have j1 := eq25617 X1
       grind)
    | exact resolve eq469 eq25617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq25617
  have eq29354 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29334 X0 X1
       have i₂ := eq671 x y
       grind)
    | (have i₁ := eq29334 X0 X1
       have i₂ := eq671 X0 (M.op (M.op x x) y)
       grind)
    | exact superpose eq671 eq29334
    | (have j0 := eq29334 X0 X0
       grind)
    | exact resolve eq29334 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29334
  have eq29363 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29354 X1 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29354
    | (have j0 := eq29354 X1 X1
       grind)
    | exact resolve eq29354 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29354
  have eq29645 : ∀ X0 : G, x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq25623 X0
       grind)
    | exact superpose eq25623 eq13
    | (have j0 := eq13 y x
       have j1 := eq25623 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25623 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq25623 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25623 X0
       grind)
    | exact resolve eq13 eq25623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25623
  have eq29663 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq29645 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29645
  have eq29680 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq29663 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29663
    | (have j0 := eq29663 X0
       grind)
    | exact resolve eq29663 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29663
  have eq29684 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq29680 X0
       grind)
    | (have r₁ := eq29680 X0
       have r₂ := eq124
       grind)
    | exact resolve eq29680 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq29680
  have eq29701 : ∀ X0 : G, (σ x) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq915 y x
       have i₂ := eq29684 X0
       grind)
    | (have i₁ := eq915 X0 x
       have i₂ := eq29684 (k X0 x)
       grind)
    | exact superpose eq29684 eq915
    | (have j1 := eq29684 X0
       grind)
    | exact resolve eq915 eq29684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq29684
  have eq29702 : ∀ X0 : G, (σ x) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq29701
    | (have j0 := eq29701 X0
       grind)
    | exact resolve eq29701 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29701
  have eq29717 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq29702 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29702
    | (have j0 := eq29702 X0
       grind)
    | exact resolve eq29702 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29702
  have eq29725 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq29717
    | (have j0 := eq29717 X0
       grind)
    | exact resolve eq29717 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29717
  have eq29731 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq29725 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29725
    | (have j0 := eq29725 X0
       grind)
    | exact resolve eq29725 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29725
  have eq29737 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq29731 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29731
    | (have j0 := eq29731 X0
       grind)
    | exact resolve eq29731 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29731
  have eq29744 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq29737
    | (have j0 := eq29737 X0
       grind)
    | exact resolve eq29737 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29737
  have eq29754 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq29744 X0
       grind)
    | (have r₁ := eq29744 X0
       have r₂ := eq27
       grind)
    | exact resolve eq29744 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29744
  have eq30541 : ∀ X0 : G, X0 ≠ X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq29363 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29363
  have eq30542 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq30541 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30541
  have eq30619 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8662 eq30542
    | exact resolve eq30542 eq8662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8662 eq30542
  have eq31008 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30619 eq765
    | exact resolve eq765 eq30619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq30619
  have eq35828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31008 eq26242
    | exact resolve eq26242 eq31008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26242 eq31008
  have eq35859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq35828
  have eq35900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq35859
    | exact resolve eq35859 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35859
  have eq35931 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq35900
       have r₂ := eq27
       grind)
    | exact resolve eq35900 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35900
  have eq35948 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ y) (σ y)) (σ x)))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35931 eq603
    | exact resolve eq603 eq35931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35931
  have eq35964 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq35948 X0
       have i₂ := eq671 sF3 sF2
       grind)
    | (have i₁ := eq35948 X0
       have i₂ := eq671 X0 (M.op (M.op sF3 sF3) sF2)
       grind)
    | exact superpose eq671 eq35948
    | exact resolve eq35948 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35948
  have eq35973 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq35964
    | exact resolve eq35964 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35964
  have eq36439 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11331 X0
       have i₂ := eq35973 x
       grind)
    | exact superpose eq35973 eq11331
    | exact resolve eq11331 eq35973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35973
  have eq37579 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36439 y
       grind)
    | exact superpose eq36439 eq18
    | (have j1 := eq36439 y
       grind)
    | exact resolve eq18 eq36439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36439
  have eq37668 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq37579
  have eq37729 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37668 eq28
    | exact resolve eq28 eq37668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37668
  have eq37888 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq37729
    | exact resolve eq37729 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq37729
  have eq38075 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37888 eq20
    | exact resolve eq20 eq37888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38125 : ∀ X0 : G, (k X0 (M.op (M.op y y) x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37888 eq219
    | exact resolve eq219 eq37888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq37888
  have eq38189 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq38125 X0
       have i₂ := eq671 y x
       grind)
    | (have i₁ := eq38125 X0
       have i₂ := eq671 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq671 eq38125
    | exact resolve eq38125 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38125
  have eq38237 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38075
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38075
    | exact resolve eq38075 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38075
  have eq38497 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38237 eq26
    | exact resolve eq26 eq38237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38237
  have eq39307 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq890 x
       have i₂ := eq38189 x
       grind)
    | exact superpose eq38189 eq890
    | (have j0 := eq890 x
       grind)
    | exact resolve eq890 eq38189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq38189
  have eq39343 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq39307
  have eq39361 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39343
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39343
    | exact resolve eq39343 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39343
  have eq39811 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39361 eq671
    | exact resolve eq671 eq39361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39361
  have eq39879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39811 eq38497
    | exact resolve eq38497 eq39811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38497 eq39811
  have eq39971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39879
  have eq40027 : x = (M.op x y) := by
    first
    | (have r₁ := eq39971
       have r₂ := eq27
       grind)
    | exact resolve eq39971 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39971
  have eq40033 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq40027 eq20
    | exact resolve eq20 eq40027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40186 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40033
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40033
    | exact resolve eq40033 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40033
  have eq40255 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40186 eq26
    | exact resolve eq26 eq40186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq40347 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq40186 eq29754
    | (have j0 := eq29754 X0
       grind)
    | (have r₁ := eq29754 X0
       have r₂ := eq40186
       grind)
    | exact resolve eq29754 eq40186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29754
  have eq40353 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq40347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40347
  have eq40558 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11527 x
       have i₂ := eq40353 y
       grind)
    | exact superpose eq40353 eq11527
    | exact resolve eq11527 eq40353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11527 eq40353
  have eq55762 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) ≠ (σ (k X0 x)) := by
    intro X0
    first
    | exact superpose eq40186 eq9504
    | (have j0 := eq9504 X0
       grind)
    | exact resolve eq9504 eq40186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9504
  have eq55763 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k X0 x)) ∨ (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq40186 eq55762
    | (have j0 := eq55762 X0
       grind)
    | exact resolve eq55762 eq40186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55762
  have eq57005 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55763 y
       have i₂ := eq40558 x
       grind)
    | exact superpose eq40558 eq55763
    | exact resolve eq55763 eq40558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40558 eq55763
  have eq57130 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57005
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57005
    | exact resolve eq57005 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57005
  have eq57210 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq57130
       have r₂ := eq20
       grind)
    | exact resolve eq57130 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57130
  have eq57250 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57210
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq57210
    | exact resolve eq57210 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57210
  have eq57275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40255 eq57250
    | exact resolve eq57250 eq40255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40255 eq57250
  have eq57286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57275
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57275
    | exact resolve eq57275 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57275
  have eq57294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq57286
    | exact resolve eq57286 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq57286
  have eq57296 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq57294
       have r₂ := eq27
       grind)
    | exact resolve eq57294 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57294
  have eq57297 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq57296 eq27
    | exact resolve eq27 eq57296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq57306 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ y) (σ y)) (σ x)))) = X0 := by
    intro X0
    first
    | exact superpose eq57296 eq603
    | exact resolve eq603 eq57296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq57296
  have eq57337 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq57306 X0
       have i₂ := eq671 sF3 sF2
       grind)
    | (have i₁ := eq57306 X0
       have i₂ := eq671 X0 (M.op (M.op sF3 sF3) sF2)
       grind)
    | exact superpose eq671 eq57306
    | exact resolve eq57306 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq57306
  have eq57353 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq57337
    | exact resolve eq57337 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq57337
  have eq57948 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11331 X0
       have i₂ := eq57353 x
       grind)
    | exact superpose eq57353 eq11331
    | exact resolve eq11331 eq57353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11331 eq57353
  have eq60907 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq57948 y
       grind)
    | exact superpose eq57948 eq18
    | (have j1 := eq57948 y
       grind)
    | exact resolve eq18 eq57948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq57948
  have eq61087 : x = y := by
    first
    | exact superpose eq40027 eq60907
    | exact resolve eq60907 eq40027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40027 eq60907
  have eq61113 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq61087
       grind)
    | exact superpose eq61087 eq24
    | exact resolve eq24 eq61087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq61087
  have eq61338 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq61113
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61113
    | exact resolve eq61113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq61113
  have eq61412 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq40186 eq61338
    | exact resolve eq61338 eq40186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40186 eq61338
  have eq61469 : False := by grind
  exact eq61469

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_y_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq74
    | (have j1 := eq93 y x
       grind)
    | exact resolve eq74 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq587 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op X0 X0) x x X3
       have i₂ := eq53 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq93
    | (have j0 := eq93 (σ y) (σ x)
       grind)
    | exact resolve eq93 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq632
    | exact resolve eq632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq636 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq633
       have r₂ := eq28
       grind)
    | exact resolve eq633 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq703 : ∀ X0 : G, y = (M.op x x) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq636 eq587
    | exact resolve eq587 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq714 : ∀ X0 X1 : G, (M.op (σ y) X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq587 x X0
       have i₂ := eq703 X1
       grind)
    | exact superpose eq703 eq587
    | (have j1 := eq703 X1
       grind)
    | exact resolve eq587 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq724 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq714 (M.op X0 X1) X1
       grind)
    | exact superpose eq714 eq13
    | (have j0 := eq13 (σ y) X0
       have j1 := eq714 X1 X1
       grind)
    | (have r₁ := eq13 (σ y) X1
       have r₂ := eq714 X0 X1
       grind)
    | (have r₁ := eq13 y X0
       have r₂ := eq714 X0 X1
       grind)
    | exact resolve eq13 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq733 : ∀ X0 X1 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq724 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq779 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X1) X0))) = (k (M.op X0 (M.op (M.op X1 X1) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       have i₂ := eq53 X0 X1 (M.op X0 X0) (M.op X1 (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq53 eq67
    | exact resolve eq67 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq67
  have eq782 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k (M.op X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq779 x X0 X2
       have i₂ := eq587 X0 x
       grind)
    | (have i₁ := eq779 X0 x X2
       have i₂ := eq587 X0 (M.op (M.op x x) X0)
       grind)
    | exact superpose eq587 eq779
    | exact resolve eq779 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq844 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq117
       have i₂ := eq733 X0 (k sF3 sF2)
       grind)
    | exact superpose eq733 eq117
    | (have j1 := eq733 X0 X0
       grind)
    | exact resolve eq117 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq733
  have eq848 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq844
    | (have j0 := eq844 X0
       grind)
    | exact resolve eq844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq851 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq848 X0
       grind)
    | (have r₁ := eq848 X0
       have r₂ := eq28
       grind)
    | exact resolve eq848 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq858 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq587 x X1
       have i₂ := eq851 X0
       grind)
    | exact superpose eq851 eq587
    | (have j1 := eq851 X1
       grind)
    | exact resolve eq587 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq851
  have eq900 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq858 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq901 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq921 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq782 y x
       have i₂ := eq901 y
       grind)
    | exact superpose eq901 eq782
    | exact resolve eq782 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq921 x
       grind)
    | exact superpose eq921 eq74
    | exact resolve eq74 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq964 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq921 y
       grind)
    | exact superpose eq921 eq75
    | exact resolve eq75 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq921
  have eq966 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq964
       have i₂ := eq901 y
       grind)
    | exact superpose eq901 eq964
    | exact resolve eq964 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq964
  have eq967 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq963
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq963
    | exact resolve eq963 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq963
  have eq969 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq966
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq966
    | exact resolve eq966 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq966
  have eq970 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq967
    | exact resolve eq967 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq967
  have eq975 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq969 eq93
    | (have j0 := eq93 (σ y) (σ y)
       grind)
    | exact resolve eq93 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq969
  have eq976 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq975
  have eq997 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq976 eq782
    | exact resolve eq782 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq976
  have eq1112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq997 eq970
    | exact resolve eq970 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq997
  have eq1120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq1112
    | exact resolve eq1112 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1112
  have eq1130 : False := by grind
  exact eq1130

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq73
    | (have j1 := eq93 x x
       grind)
    | exact resolve eq73 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq586 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op X0 X0) x x X3
       have i₂ := eq52 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq117 eq93
    | (have j0 := eq93 x (σ x)
       grind)
    | exact resolve eq93 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq633
    | exact resolve eq633 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq637 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq634
       have r₂ := eq27
       grind)
    | exact resolve eq634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq702 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq637 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq637
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq637
       grind)
    | exact resolve eq13 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq708 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq702
  have eq727 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq708 eq49
    | exact resolve eq49 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq708
  have eq731 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq727
    | exact resolve eq727 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq727
  have eq959 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq93 x x
       have i₂ := eq731
       grind)
    | exact superpose eq731 eq93
    | (have j0 := eq93 x x
       grind)
    | exact resolve eq93 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq960 : x = (M.op x x) := by grind
  clear eq959
  have eq967 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq960
       grind)
    | exact superpose eq960 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq960
       grind)
    | exact resolve eq13 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq586 x X0
       have i₂ := eq960
       grind)
    | exact superpose eq960 eq586
    | exact resolve eq586 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq974 : x = (k x x) := by grind
  clear eq967
  have eq1034 : y = (M.op x y) := by
    first
    | (have i₁ := eq970 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq970
    | (have j0 := eq970 y
       grind)
    | exact resolve eq970 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq970
  have eq1067 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1034 eq20
    | exact resolve eq20 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1034
  have eq1088 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1067
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1067
    | exact resolve eq1067 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1067
  have eq1090 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1088 eq26
    | exact resolve eq26 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1088
  have eq1112 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq974
       grind)
    | exact superpose eq974 eq43
    | exact resolve eq43 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq974
  have eq1116 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1112
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1112
    | exact resolve eq1112 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1112
  have eq1204 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1116 eq93
    | (have j0 := eq93 x (σ x)
       grind)
    | exact resolve eq93 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1116
  have eq1205 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1204
  have eq1236 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1205 eq586
    | exact resolve eq586 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq1205
  have eq1332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1236 eq1090
    | exact resolve eq1090 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq1236
  have eq1367 : False := by grind
  exact eq1367

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
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
  have eq74 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq44
    | exact resolve eq44 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq50
    | exact resolve eq50 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq76 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq75
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq75
    | exact resolve eq75 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq74
    | exact resolve eq74 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq74
  have eq100 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq19098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq19098
    | exact resolve eq19098 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19098
  have eq19110 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq19099
       have r₂ := eq28
       grind)
    | exact resolve eq19099 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19099
  have eq19114 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq19110
    | exact resolve eq19110 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19110
  have eq19116 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq19114 eq65
    | (have r₁ := eq65
       have r₂ := eq19114
       grind)
    | exact resolve eq65 eq19114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq19114
  have eq19161 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq19116
  have eq19363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq19161 eq117
    | exact resolve eq117 eq19161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq19161
  have eq19376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19363
  have eq19379 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19376
       have r₂ := eq28
       grind)
    | exact resolve eq19376 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19376
  have eq19381 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq19379
       grind)
    | exact superpose eq19379 eq64
    | (have r₁ := eq64
       have r₂ := eq19379
       grind)
    | exact resolve eq64 eq19379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq19382 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq19379
       grind)
    | exact superpose eq19379 eq77
    | exact resolve eq77 eq19379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq19379
  have eq19425 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq19381
  have eq19440 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq19382
    | exact resolve eq19382 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19382
  have eq19711 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19425
       grind)
    | exact superpose eq19425 eq100
    | exact resolve eq100 eq19425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq19425
  have eq19735 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq19711
    | exact resolve eq19711 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19711
  have eq20397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19735 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq19735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19735
  have eq20398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq20397
  have eq20402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq20398
    | exact resolve eq20398 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20398
  have eq20413 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq20402
       have r₂ := eq28
       grind)
    | exact resolve eq20402 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20402
  have eq20417 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq20413
    | exact resolve eq20413 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20413
  have eq20431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20417 eq19440
    | exact resolve eq19440 eq20417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19440 eq20417
  have eq20465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20431
  have eq20471 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20465
       have r₂ := eq28
       grind)
    | exact resolve eq20465 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20465
  have eq20474 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq20471 eq30
    | exact resolve eq30 eq20471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20471
  have eq20605 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq20474
    | exact resolve eq20474 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20474
  have eq20606 : x = y := by grind
  clear eq20605
  have eq20751 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20606
       grind)
    | exact superpose eq20606 eq19
    | exact resolve eq19 eq20606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20752 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20606
       grind)
    | exact superpose eq20606 eq25
    | exact resolve eq25 eq20606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20606
  have eq20868 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20752
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20752
    | exact resolve eq20752 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20752
  have eq20883 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20868 eq27
    | exact resolve eq27 eq20868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20868
  have eq21130 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20883 eq76
    | exact resolve eq76 eq20883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq20883
  have eq21187 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21130
       have i₂ := eq20751
       grind)
    | exact superpose eq20751 eq21130
    | exact resolve eq21130 eq20751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20751 eq21130
  have eq21199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21187 eq15
    | exact resolve eq15 eq21187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21187
  have eq21245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq21199
    | exact resolve eq21199 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21199
  have eq21254 : False := by grind
  exact eq21254

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_pyy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44
    | (have j0 := eq44 (σ X0) (σ X1)
       grind)
    | exact resolve eq44 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq35 (τ X0) X1 X2
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35
  have eq86 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq110 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 (M.op (M.op X1 X1) X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq24 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq24 eq86
    | exact resolve eq86 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq151 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op X0 X0) x x X3
       have i₂ := eq24 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq176 : ∀ X0 X1 X2 X3 X4 : G, (k X3 (σ (M.op X4 (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X4)))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq110 X4 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3
       have i₂ := eq25 X0 X1 X2 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0)
       grind)
    | exact superpose eq25 eq110
    | exact resolve eq110 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq191 : ∀ X3 X4 : G, (k X3 (σ (M.op X4 X4))) = X3 := by
    intro X3 X4
    first
    | (have i₁ := eq176 x x x X3 X4
       have i₂ := eq25 x x x X4
       grind)
    | exact superpose eq25 eq176
    | exact resolve eq176 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq176
  have eq201 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 y x
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq224 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ (M.op X1 X1))
       have i₂ := eq191 (σ X0) X1
       grind)
    | exact superpose eq191 eq31
    | exact resolve eq31 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq229 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq224
    | exact resolve eq224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq230 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq229
    | exact resolve eq229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq237 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (M.op X1 X1)
       have i₂ := eq230 (σ X0) X1
       grind)
    | exact superpose eq230 eq31
    | exact resolve eq31 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq241 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq237
    | exact resolve eq237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq770 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq201
       have i₂ := eq44 y x
       grind)
    | exact superpose eq44 eq201
    | (have j1 := eq44 (σ y) (σ x)
       grind)
    | exact resolve eq201 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq201
  have eq771 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq770
  have eq1507 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq151 y X0
       have i₂ := eq771
       grind)
    | exact superpose eq771 eq151
    | exact resolve eq151 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq1963 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq212 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq212
    | (have j0 := eq212 (τ X0)
       grind)
    | exact resolve eq212 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1994 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1963 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1963
    | (have j0 := eq1963 X0
       grind)
    | exact resolve eq1963 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963
  have eq2010 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1994 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1994
    | (have j0 := eq1994 X0
       grind)
    | exact resolve eq1994 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq2143 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 (σ y)
       have i₂ := eq1507 X1
       grind)
    | exact superpose eq1507 eq241
    | (have j1 := eq1507 X1
       grind)
    | exact resolve eq241 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1507
  have eq2176 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2143 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2143
    | (have j0 := eq2143 X0 X1
       grind)
    | exact resolve eq2143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2180 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2010 x
       have i₂ := eq2176 x X0
       grind)
    | exact superpose eq2176 eq2010
    | (have j0 := eq2010 x
       have j1 := eq2176 X0 x
       grind)
    | (have r₁ := eq2010 x
       have r₂ := eq2176 x x
       grind)
    | exact resolve eq2010 eq2176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010 eq2176
  have eq2193 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2180 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq2237 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq2193 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2238 : x = (M.op x x) := by grind
  clear eq2237
  have eq2256 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq151 x X0
       have i₂ := eq2238
       grind)
    | exact superpose eq2238 eq151
    | exact resolve eq151 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2259 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq230 X0 x
       have i₂ := eq2238
       grind)
    | exact superpose eq2238 eq230
    | exact resolve eq230 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq2238
  have eq2378 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq212 x
       have i₂ := eq2259 x
       grind)
    | exact superpose eq2259 eq212
    | (have j0 := eq212 x
       grind)
    | exact resolve eq212 eq2259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq2259
  have eq2389 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2378
  have eq4700 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq151 (σ x) X0
       have i₂ := eq2389
       grind)
    | exact superpose eq2389 eq151
    | exact resolve eq151 eq2389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq2389
  have eq4760 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4700 (σ y)
       grind)
    | exact superpose eq4700 eq16
    | exact resolve eq16 eq4700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4700
  have eq4877 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4760
       have i₂ := eq2256 y
       grind)
    | exact superpose eq2256 eq4760
    | exact resolve eq4760 eq2256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256 eq4760
  have eq4878 : False := by grind
  exact eq4878

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then X else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_x_pyx_pxy_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq176 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
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
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq180 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq182 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | exact superpose eq176 eq13
    | (have j0 := eq13 X0 (M.op (M.op y (M.op x y)) x)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq176 X0
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq183 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq187 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       have r₂ := eq177 X0
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq329 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op y (M.op x y)) x))) := by
    intro X0
    first
    | exact superpose eq185 eq34
    | exact resolve eq34 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (k X0 (σ (M.op (M.op y (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq329 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq329
    | exact resolve eq329 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq398 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq477 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)))) := by
    intro X0
    first
    | exact superpose eq189 eq398
    | exact resolve eq398 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq503 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq477 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq477
    | exact resolve eq477 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq717 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq718 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 (M.op X1 X0)) X1) X2) = X2 ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq11 X0 (M.op X1 X0)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op X1 X0)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (M.op (M.op (k y (M.op x y)) x) X0) = X0 ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq758 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq771 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 (M.op X2 X1)) X2) = (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) ∨ (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq12
    | (have j0 := eq12 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) ∨ (M.op (M.op X1 (M.op X2 X1)) X2) = (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq771 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq786 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq760 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq760
    | (have j0 := eq760 (σ X0)
       grind)
    | exact resolve eq760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq181
    | exact resolve eq181 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq839 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq181 (τ X0) X1 X2
       grind)
    | exact superpose eq181 eq34
    | exact resolve eq34 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq844 : ∀ X0 X1 : G, (τ (σ x)) = (k x (τ (M.op (M.op X0 (M.op X1 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (M.op (M.op X1 (M.op x X1)) x)
       have i₂ := eq181 sF2 X1 x
       grind)
    | exact superpose eq181 eq90
    | exact resolve eq90 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 X1 : G, x = (k x (τ (M.op (M.op X0 (M.op X1 X0)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq29 eq844
    | exact resolve eq844 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq853 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq839 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq839
    | exact resolve eq839 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq1212 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq717
       grind)
    | exact superpose eq717 eq40
    | exact resolve eq40 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1212
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1212
    | exact resolve eq1212 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1215 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq1213
    | exact resolve eq1213 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1511 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq182 eq184
    | exact resolve eq184 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq184
  have eq3914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1215 eq718
    | exact resolve eq718 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3924 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq3914
       have r₂ := eq27
       grind)
    | exact resolve eq3914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3914
  have eq3934 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ x)) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3924 eq181
    | exact resolve eq181 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq3936 : x = (k x (τ (M.op (M.op (σ x) (σ x)) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3924 eq848
    | exact resolve eq848 eq3924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq3924
  have eq3951 : x = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3936
       have i₂ := eq1511 sF2 sF3
       grind)
    | exact superpose eq1511 eq3936
    | exact resolve eq3936 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq3953 : ∀ X0 : G, x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3934 X0
       have i₂ := eq1511 sF2 sF3
       grind)
    | exact superpose eq1511 eq3934
    | exact resolve eq3934 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3934
  have eq3962 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31 eq3951
    | exact resolve eq3951 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3951
  have eq3966 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq3962
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq3962
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq3962
       have r₂ := eq13 x y
       grind)
    | exact resolve eq3962 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3962
  have eq3968 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq717
       have i₂ := eq3966
       grind)
    | exact superpose eq3966 eq717
    | exact resolve eq717 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq3970 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq3966
       grind)
    | exact superpose eq3966 eq40
    | exact resolve eq40 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3966
  have eq3973 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3968
  have eq3978 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3970
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3970
    | exact resolve eq3970 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3970
  have eq3984 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3978 eq1215
    | exact resolve eq1215 eq3978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq3985 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3978 eq718
    | exact resolve eq718 eq3978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3978
  have eq3991 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3985
  have eq3992 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3984
  have eq4003 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3973
       grind)
    | exact superpose eq3973 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3973
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3973
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3973
       grind)
    | exact resolve eq12 eq3973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq4018 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4003
  have eq4031 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4018
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4018
    | exact resolve eq4018 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4018
  have eq4032 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4031
  have eq4038 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4032
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4032
    | exact resolve eq4032 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4032
  have eq4040 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3991 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3991
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3991
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3991
       grind)
    | exact resolve eq12 eq3991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991
  have eq4055 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4040
  have eq4068 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4055
    | exact resolve eq4055 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4055
  have eq4069 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4068
  have eq4075 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4069
    | exact resolve eq4069 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4069
  have eq4077 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3992
       grind)
    | exact superpose eq3992 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3992
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3992
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3992
       grind)
    | exact resolve eq12 eq3992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq4092 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4077
  have eq4105 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4092
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4092
    | exact resolve eq4092 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4092
  have eq4106 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4105
  have eq4112 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4106
    | exact resolve eq4106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106
  have eq4352 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq4038
       grind)
    | exact superpose eq4038 eq39
    | exact resolve eq39 eq4038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4038
  have eq4355 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4352
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4352
    | exact resolve eq4352 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4352
  have eq4357 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4355
    | exact resolve eq4355 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4355
  have eq5201 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq4112
       grind)
    | exact superpose eq4112 eq39
    | exact resolve eq39 eq4112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq4112
  have eq5205 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5201
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5201
    | exact resolve eq5201 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5201
  have eq5207 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5205
    | exact resolve eq5205 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5205
  have eq5312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4357 eq4075
    | exact resolve eq4075 eq4357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357
  have eq5319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5312
  have eq5324 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5319
       have r₂ := eq27
       grind)
    | exact resolve eq5319 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319
  have eq5341 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ y) (σ y)) (σ x)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5324 eq503
    | exact resolve eq503 eq5324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5324
  have eq5383 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5341 X0
       have i₂ := eq1511 sF3 sF2
       grind)
    | exact superpose eq1511 eq5341
    | exact resolve eq5341 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5341
  have eq5404 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq5383
    | exact resolve eq5383 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5383
  have eq5889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5207 eq4075
    | exact resolve eq4075 eq5207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4075
  have eq5896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5889
  have eq5901 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq5896
       have r₂ := eq27
       grind)
    | exact resolve eq5896 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5896
  have eq5920 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ y) (σ y)) (σ x)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq5901 eq503
    | exact resolve eq503 eq5901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5901
  have eq5962 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq5920 X0
       have i₂ := eq1511 sF3 sF2
       grind)
    | exact superpose eq1511 eq5920
    | exact resolve eq5920 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5920
  have eq5983 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq29 eq5962
    | exact resolve eq5962 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5962
  have eq6462 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq760 x
       have i₂ := eq5404 x
       grind)
    | exact superpose eq5404 eq760
    | (have j0 := eq760 x
       grind)
    | (have r₁ := eq760 x
       have r₂ := eq5404 x
       grind)
    | exact resolve eq760 eq5404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5404
  have eq6478 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6462
  have eq7569 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq760 x
       have i₂ := eq5983 x
       grind)
    | exact superpose eq5983 eq760
    | (have j0 := eq760 x
       grind)
    | (have r₁ := eq760 x
       have r₂ := eq5983 x
       grind)
    | exact resolve eq760 eq5983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5983
  have eq7585 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq7569
  have eq7606 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1511 x X0
       have i₂ := eq6478
       grind)
    | exact superpose eq6478 eq1511
    | exact resolve eq1511 eq6478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6478
  have eq7716 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1511 x X0
       have i₂ := eq7585
       grind)
    | exact superpose eq7585 eq1511
    | exact resolve eq1511 eq7585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7585
  have eq7823 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7606 y
       grind)
    | exact superpose eq7606 eq18
    | (have j1 := eq7606 y
       grind)
    | exact resolve eq18 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606
  have eq7913 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq7823
  have eq7963 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7913 eq27
    | exact resolve eq27 eq7913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7968 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (σ x)) (σ x))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7913 eq189
    | exact resolve eq189 eq7913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq7976 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ y) (σ x)) (σ x)))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7913 eq503
    | exact resolve eq503 eq7913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7913
  have eq8004 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7716 y
       grind)
    | exact superpose eq7716 eq18
    | (have j1 := eq7716 y
       grind)
    | exact resolve eq18 eq7716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7716
  have eq8094 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq8004
  have eq8901 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op x x) y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq853 X0 x y
       have i₂ := eq3953 X1
       grind)
    | exact superpose eq3953 eq853
    | (have j1 := eq3953 X1
       grind)
    | exact resolve eq853 eq3953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq3953
  have eq8907 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8901 X0 X1
       have i₂ := eq1511 x y
       grind)
    | exact superpose eq1511 eq8901
    | (have j0 := eq8901 X0 X0
       grind)
    | exact resolve eq8901 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8901
  have eq8922 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8907 X1 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8907
    | (have j0 := eq8907 X1 X1
       grind)
    | exact resolve eq8907 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8907
  have eq9440 : ∀ X0 : G, X0 ≠ X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq8922 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8922
  have eq9441 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq9440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9440
  have eq9452 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9441 eq760
    | (have j0 := eq760 (σ y)
       grind)
    | (have r₁ := eq760 (σ y)
       have r₂ := eq9441 (σ y)
       grind)
    | exact resolve eq760 eq9441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9469 : (τ (σ y)) = (k y (τ (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9441 eq107
    | exact resolve eq107 eq9441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq9441
  have eq9472 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9452
  have eq9475 : y = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq9469
    | exact resolve eq9469 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9469
  have eq9544 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = (k (M.op (M.op (σ y) (σ y)) (σ y)) X0) ∨ (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9472 eq778
    | exact resolve eq778 eq9472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq9472
  have eq9564 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9544 X0
       have i₂ := eq1511 sF3 sF3
       grind)
    | exact superpose eq1511 eq9544
    | (have j0 := eq9544 X0
       grind)
    | exact resolve eq9544 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9544
  have eq9596 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9564 X0
       have i₂ := eq1511 sF3 sF3
       grind)
    | exact superpose eq1511 eq9564
    | (have j0 := eq9564 X0
       grind)
    | exact resolve eq9564 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9564
  have eq9603 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq758 y y
       have i₂ := eq9475
       grind)
    | exact superpose eq9475 eq758
    | (have j0 := eq758 y y
       grind)
    | (have r₁ := eq758 y y
       have r₂ := eq9475
       grind)
    | exact resolve eq758 eq9475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9475
  have eq9604 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9603
  have eq9605 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9604
  have eq9841 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1511 y X0
       have i₂ := eq9605
       grind)
    | exact superpose eq9605 eq1511
    | exact resolve eq1511 eq9605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9605
  have eq33429 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9596
    | (have j0 := eq9596 (σ x)
       grind)
    | exact resolve eq9596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9596
  have eq33711 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq33429
  have eq33909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33711 eq5207
    | exact resolve eq5207 eq33711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq33929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33909
  have eq33944 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33929
       have r₂ := eq27
       grind)
    | exact resolve eq33929 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33929
  have eq33951 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8094 eq33944
    | exact resolve eq33944 eq8094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8094 eq33944
  have eq33958 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33951 eq31
    | exact resolve eq31 eq33951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq34053 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33951 eq7968
    | exact resolve eq7968 eq33951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7968
  have eq34055 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ x)) (σ x)))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33951 eq7976
    | exact resolve eq7976 eq33951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7976 eq33951
  have eq34159 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ x)) (σ x)))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq34055 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34055
  have eq34161 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq34053 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34053
  have eq34220 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ x)) (σ x)))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34159 X0
       grind)
    | (have r₁ := eq34159 X0
       have r₂ := eq7963
       grind)
    | exact resolve eq34159 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34159
  have eq34222 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34161 X0
       grind)
    | (have r₁ := eq34161 X0
       have r₂ := eq7963
       grind)
    | exact resolve eq34161 eq7963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34161
  have eq34271 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq33958
    | exact resolve eq33958 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33958
  have eq34277 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34220 X0
       have i₂ := eq1511 sF2 sF2
       grind)
    | exact superpose eq1511 eq34220
    | exact resolve eq34220 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34220
  have eq34279 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34222 X0
       have i₂ := eq1511 sF2 sF2
       grind)
    | exact superpose eq1511 eq34222
    | exact resolve eq34222 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34222
  have eq34312 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq34277
    | exact resolve eq34277 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34277
  have eq34431 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq34271 eq7963
    | (have r₁ := eq7963
       have r₂ := eq34271
       grind)
    | exact resolve eq7963 eq34271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7963 eq34271
  have eq34434 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq34431
  have eq34435 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq34434
  have eq34924 : ∀ X0 : G, (k X0 (M.op (M.op (M.op x y) (M.op x y)) x)) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq34435
       grind)
    | exact superpose eq34435 eq185
    | exact resolve eq185 eq34435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq34932 : ∀ X0 : G, (k X0 (σ (M.op (M.op (M.op x y) (M.op x y)) x))) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq359 X0
       have i₂ := eq34435
       grind)
    | exact superpose eq34435 eq359
    | exact resolve eq359 eq34435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34435
  have eq34997 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq34932 X0
       have i₂ := eq1511 sF0 x
       grind)
    | exact superpose eq1511 eq34932
    | exact resolve eq34932 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34932
  have eq35004 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq34924 X0
       have i₂ := eq1511 sF0 x
       grind)
    | exact superpose eq1511 eq34924
    | exact resolve eq34924 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34924
  have eq35032 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq34997 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34997
    | (have j0 := eq34997 X0
       grind)
    | exact resolve eq34997 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34997
  have eq35042 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34312 eq35004
    | (have j0 := eq35004 X0
       have j1 := eq34312 X0
       grind)
    | exact resolve eq35004 eq34312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34312 eq35004
  have eq35043 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq35042 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35042
  have eq35063 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34279 eq35032
    | (have j0 := eq35032 X0
       have j1 := eq34279 X0
       grind)
    | exact resolve eq35032 eq34279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34279 eq35032
  have eq35064 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq35063 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35063
  have eq35084 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq760 x
       have i₂ := eq35043 x
       grind)
    | exact superpose eq35043 eq760
    | (have j0 := eq760 x
       grind)
    | (have r₁ := eq760 x
       have r₂ := eq35043 x
       grind)
    | exact resolve eq760 eq35043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35043
  have eq35107 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq35084
  have eq35146 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35064 eq760
    | (have j0 := eq760 (σ x)
       grind)
    | (have r₁ := eq760 (σ x)
       have r₂ := eq35064 (σ x)
       grind)
    | exact resolve eq760 eq35064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35064
  have eq35179 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq35146
  have eq35221 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1511 x X0
       have i₂ := eq35107
       grind)
    | exact superpose eq35107 eq1511
    | exact resolve eq1511 eq35107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35107
  have eq35327 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35179 eq1511
    | exact resolve eq1511 eq35179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35179
  have eq35431 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35221 y
       grind)
    | exact superpose eq35221 eq18
    | (have j1 := eq35221 y
       grind)
    | exact resolve eq18 eq35221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35221
  have eq35643 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq35431
       grind)
    | exact superpose eq35431 eq24
    | exact resolve eq24 eq35431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35431
  have eq35727 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq35643
    | exact resolve eq35643 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35643
  have eq36760 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35327 eq26
    | (have j1 := eq35327 (σ y)
       grind)
    | exact resolve eq26 eq35327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35327
  have eq36948 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36760 eq27
    | exact resolve eq27 eq36760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36760
  have eq37017 : x = (M.op x y) := by
    first
    | (have r₁ := eq36948
       have r₂ := eq35727
       grind)
    | exact resolve eq36948 eq35727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35727 eq36948
  have eq37032 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq37017
       grind)
    | exact superpose eq37017 eq18
    | exact resolve eq18 eq37017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37033 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq37017
       grind)
    | exact superpose eq37017 eq22
    | exact resolve eq22 eq37017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37116 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq37033 eq20
    | exact resolve eq20 eq37033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37272 : ∀ X0 : G, (M.op (M.op (k y (M.op x y)) (M.op x y)) X0) = X0 ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq37032 eq721
    | (have j0 := eq721 y x x
       grind)
    | exact resolve eq721 eq37032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq37285 : ∀ X0 : G, y = (M.op x y) ∨ (M.op (M.op (k y (M.op x y)) (M.op x y)) X0) = X0 ∨ (M.op x y) = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq37032 eq37272
    | (have j0 := eq37272 X0
       grind)
    | exact resolve eq37272 eq37032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37272
  have eq43081 : ∀ X0 : G, (k X0 (M.op (M.op (k y (M.op x y)) x) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)))) = X0 ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq742 eq829
    | exact resolve eq829 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq829
  have eq43270 : ∀ X0 : G, (k X0 (M.op (M.op (k y (M.op x y)) (M.op x y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)))) = X0 ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq43081 X0
       have i₂ := eq37017
       grind)
    | exact superpose eq37017 eq43081
    | exact resolve eq43081 eq37017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43081
  have eq43315 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 (M.op (M.op (k y (M.op x y)) (M.op x y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)))) = X0 ∨ (M.op x y) = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq37032 eq43270
    | (have j0 := eq43270 X0
       grind)
    | exact resolve eq43270 eq37032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43270
  have eq43330 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 (M.op (M.op (k y (M.op x y)) (M.op x y)) (M.op (M.op (σ y) (σ y)) (σ x)))) = X0 ∨ (M.op x y) = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq9841 eq43315
    | (have j1 := eq9841 (M.op x y)
       grind)
    | exact resolve eq43315 eq9841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9841 eq43315
  have eq43339 : ∀ X0 : G, (k X0 (M.op (M.op (k y (M.op x y)) (M.op x y)) (σ x))) = X0 ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq43330 X0
       have i₂ := eq1511 sF3 sF2
       grind)
    | exact superpose eq1511 eq43330
    | exact resolve eq43330 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43330
  have eq43343 : ∀ X0 : G, (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq37285 eq43339
    | exact resolve eq43339 eq37285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37285 eq43339
  have eq43577 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq43343 (M.op X0 x)
       grind)
    | exact superpose eq43343 eq12
    | (have j0 := eq12 y (M.op x y)
       have j1 := eq43343 X0
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq43343 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq43343 X0
       grind)
    | exact resolve eq12 eq43343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43579 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) y) X0) = X0 ∨ y = (M.op x y) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq43343 (M.op x X1)
       grind)
    | exact superpose eq43343 eq16
    | (have j1 := eq43343 X1
       grind)
    | exact resolve eq16 eq43343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43343
  have eq43598 : ∀ X0 : G, y = (M.op (M.op x y) y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq43577 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43577
  have eq43614 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43579 X0 X1
       have i₂ := eq1511 sF0 y
       grind)
    | exact superpose eq1511 eq43579
    | (have j0 := eq43579 X0 X1
       grind)
    | exact resolve eq43579 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43579
  have eq43615 : ∀ X0 : G, y = (M.op x y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq37032 eq43598
    | (have j0 := eq43598 X0
       grind)
    | exact resolve eq43598 eq37032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43598
  have eq43616 : ∀ X0 : G, y = (M.op x y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq43615 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43615
  have eq43655 : ∀ X0 : G, (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq37032 eq43616
    | (have j0 := eq43616 X0
       grind)
    | exact resolve eq43616 eq37032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43616
  have eq43989 : ∀ X0 : G, (τ (σ x)) = (k x (τ (σ x))) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq43614 (k sF2 X0) x
       grind)
    | exact superpose eq43614 eq90
    | (have j1 := eq43614 X0 x
       grind)
    | exact resolve eq90 eq43614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq43614
  have eq44014 : ∀ X0 : G, x = (k x x) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq43989
    | (have j0 := eq43989 X0
       grind)
    | exact resolve eq43989 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43989
  have eq44035 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44014 X0
       have i₂ := eq37017
       grind)
    | exact superpose eq37017 eq44014
    | (have j0 := eq44014 X0
       grind)
    | exact resolve eq44014 eq37017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44014
  have eq44323 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq43655 (k y X0)
       grind)
    | exact superpose eq43655 eq36
    | (have j1 := eq43655 X0
       grind)
    | exact resolve eq36 eq43655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq43655
  have eq44343 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq44323
    | (have j0 := eq44323 X0
       grind)
    | exact resolve eq44323 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq44323
  have eq44346 : ∀ X0 : G, (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq37116 eq44343
    | (have j0 := eq44343 X0
       grind)
    | exact resolve eq44343 eq37116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44343
  have eq44867 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq758 X0 x
       have i₂ := eq44035 (k X0 x)
       grind)
    | exact superpose eq44035 eq758
    | (have j0 := eq758 (M.op x y) (M.op x y)
       have j1 := eq44035 X0
       grind)
    | (have r₁ := eq758 (M.op x y) (M.op x y)
       have r₂ := eq44035 X0
       grind)
    | exact resolve eq758 eq44035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758 eq44035
  have eq44868 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq44867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44867
  have eq44869 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq44868 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44868
  have eq45101 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq33711
       have i₂ := eq44346 (k sF3 sF2)
       grind)
    | exact superpose eq44346 eq33711
    | (have j1 := eq44346 X0
       grind)
    | exact resolve eq33711 eq44346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44346
  have eq45131 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq45101 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45101
  have eq47222 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1511 X0 X1
       have i₂ := eq44869 (M.op X0 X0)
       grind)
    | exact superpose eq44869 eq1511
    | (have j1 := eq44869 X1
       grind)
    | exact resolve eq1511 eq44869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44869
  have eq48023 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37032
       have i₂ := eq47222 X0 (M.op sF0 y)
       grind)
    | exact superpose eq47222 eq37032
    | (have j1 := eq47222 X0 X0
       grind)
    | exact resolve eq37032 eq47222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47222
  have eq48197 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq48023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48023
  have eq48380 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq48197 X0
       grind)
    | exact superpose eq48197 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq48197 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq48197 X0
       grind)
    | exact resolve eq13 eq48197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48197
  have eq48504 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq48380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48380
  have eq48642 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq786 y
       have i₂ := eq48504 y
       grind)
    | exact superpose eq48504 eq786
    | (have j0 := eq786 y
       grind)
    | exact resolve eq786 eq48504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq48504
  have eq48666 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq48642
  have eq48682 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq48666
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48666
    | exact resolve eq48666 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48666
  have eq48787 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq48682 eq1511
    | exact resolve eq1511 eq48682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48682
  have eq48939 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ x)))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq48787 eq503
    | exact resolve eq503 eq48787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq72820 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45131 eq33711
    | exact resolve eq33711 eq45131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33711 eq45131
  have eq72826 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq72820
  have eq72886 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (σ x)))) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq72826 eq48939
    | exact resolve eq48939 eq72826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48939 eq72826
  have eq72896 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (σ x)))) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq72886 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72886
  have eq72909 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq48787 eq72896
    | exact resolve eq72896 eq48787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48787 eq72896
  have eq72947 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq72909
    | exact resolve eq72909 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq72909
  have eq72964 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq72947 X0
       have i₂ := eq37017
       grind)
    | exact superpose eq37017 eq72947
    | exact resolve eq72947 eq37017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37017 eq72947
  have eq76418 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72964 eq760
    | (have j0 := eq760 (M.op x y)
       grind)
    | (have r₁ := eq760 (M.op x y)
       have r₂ := eq72964 (M.op x y)
       grind)
    | exact resolve eq760 eq72964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq72964
  have eq76470 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq76418
  have eq76578 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq76470 eq1511
    | exact resolve eq1511 eq76470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76470
  have eq76754 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76578 eq37032
    | exact resolve eq37032 eq76578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37032 eq76578
  have eq76968 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq76754
  have eq77085 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76968 eq27
    | exact resolve eq27 eq76968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76968
  have eq77197 : y = (M.op x y) := by
    first
    | (have r₁ := eq77085
       have r₂ := eq37116
       grind)
    | exact resolve eq77085 eq37116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77085
  have eq77208 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq77197
       grind)
    | exact superpose eq77197 eq24
    | exact resolve eq24 eq77197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq77223 : ∀ X0 : G, (k X0 (σ (M.op (M.op (M.op x y) (M.op x y)) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq359 X0
       have i₂ := eq77197
       grind)
    | exact superpose eq77197 eq359
    | exact resolve eq359 eq77197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq77197
  have eq77322 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq77223 X0
       have i₂ := eq1511 sF0 x
       grind)
    | exact superpose eq1511 eq77223
    | exact resolve eq77223 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511 eq77223
  have eq77336 : (σ x) = (σ y) := by
    first
    | exact superpose eq37033 eq77208
    | exact resolve eq77208 eq37033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37033 eq77208
  have eq77363 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq77322 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq77322
    | (have j0 := eq77322 X0
       grind)
    | exact resolve eq77322 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq77322
  have eq77380 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq77336 eq26
    | exact resolve eq26 eq77336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq77417 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq77336 eq718
    | exact resolve eq718 eq77336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq77336
  have eq77605 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq77363 eq77417
    | exact resolve eq77417 eq77363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77363 eq77417
  have eq77606 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq77605
  have eq77622 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77380 eq77606
    | exact resolve eq77606 eq77380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77380 eq77606
  have eq77623 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq77622
  have eq77648 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq77623 eq27
    | exact resolve eq27 eq77623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq77623
  have eq77739 : False := by grind
  exact eq77739

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) := by
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
  have eq69 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq83 y x
       grind)
    | exact superpose eq83 eq75
    | (have j1 := eq83 y x
       grind)
    | exact resolve eq75 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq121 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq82
    | exact resolve eq82 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq83
    | (have j0 := eq83 (σ y) (σ x)
       grind)
    | exact resolve eq83 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq124 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq121
    | exact resolve eq121 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq121
  have eq126 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq123
       have r₂ := eq27
       grind)
    | exact resolve eq123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq142 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq64
    | exact resolve eq64 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq143 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq27
    | exact resolve eq27 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq83 (σ X0) sF2
       grind)
    | exact superpose eq83 eq39
    | (have j1 := eq83 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq220 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq13
    | (have r₁ := eq13 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq50 X0
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (k X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq225 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq13
    | (have r₁ := eq13 X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))
       have r₂ := eq51 X0
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq228 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq435 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq69
    | (have r₁ := eq69
       have r₂ := eq128
       grind)
    | exact resolve eq69 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq128
  have eq436 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq435
  have eq439 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq436 eq115
    | exact resolve eq115 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq436 eq82
    | exact resolve eq82 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq436
  have eq442 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq439
  have eq445 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq440
    | exact resolve eq440 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq440
  have eq458 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq442 eq115
    | exact resolve eq115 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq459 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq442 eq142
    | (have r₁ := eq142
       have r₂ := eq442
       grind)
    | exact resolve eq142 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq442
  have eq482 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq459
  have eq483 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq482
  have eq484 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq458
  have eq592 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq445
       grind)
    | exact superpose eq445 eq124
    | exact resolve eq124 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq445
  have eq595 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq592
  have eq626 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op X0 X0) x x X3
       have i₂ := eq52 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq763 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq484 eq483
    | exact resolve eq483 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq484
  have eq766 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq763
  have eq769 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq766
       have r₂ := eq143
       grind)
    | exact resolve eq766 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq773 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq769 eq26
    | exact resolve eq26 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq769 eq595
    | exact resolve eq595 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq769
  have eq797 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq796
  have eq813 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq797
       have r₂ := eq143
       grind)
    | exact resolve eq797 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq797
  have eq856 : ∀ X0 : G, (M.op (M.op (M.op y y) x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq813 eq50
    | exact resolve eq50 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq813
  have eq870 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq856 X0
       have i₂ := eq626 y x
       grind)
    | (have i₁ := eq856 X0
       have i₂ := eq626 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq626 eq856
    | exact resolve eq856 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq902 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq870 X0
       grind)
    | exact superpose eq870 eq13
    | (have r₁ := eq13 X0 x
       have r₂ := eq870 X0
       grind)
    | exact resolve eq13 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq911 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq950 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43
       have i₂ := eq911 x
       grind)
    | exact superpose eq911 eq43
    | exact resolve eq43 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq911
  have eq961 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq950
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq950
    | exact resolve eq950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq967 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq961 eq83
    | (have j0 := eq83 (σ x) (σ x)
       grind)
    | exact resolve eq83 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq968 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq967
  have eq1001 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq968 eq626
    | exact resolve eq626 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1001 eq773
    | exact resolve eq773 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq1001
  have eq1032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1015
  have eq1041 : x = (M.op x y) := by
    first
    | (have r₁ := eq1032
       have r₂ := eq27
       grind)
    | exact resolve eq1032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1046 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1041 eq20
    | exact resolve eq20 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1050 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq1041 eq68
    | (have r₁ := eq68
       have r₂ := eq1041
       grind)
    | exact resolve eq68 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1055 : y = (k y x) ∨ x = y := by grind
  clear eq1050
  have eq1062 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1046
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1046
    | exact resolve eq1046 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1064 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1062 eq26
    | exact resolve eq26 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1117 : ∀ X0 : G, (k X0 (M.op (M.op y x) x)) = X0 := by
    intro X0
    first
    | exact superpose eq1041 eq223
    | exact resolve eq223 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1122 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq1062 eq228
    | exact resolve eq228 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq1135 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq1055
       grind)
    | exact superpose eq1055 eq75
    | exact resolve eq75 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1055
  have eq1138 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1062 eq1135
    | exact resolve eq1135 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1142 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1138
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1138
    | exact resolve eq1138 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1153 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1142 eq83
    | (have j0 := eq83 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq83 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1155 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1064 eq1153
    | exact resolve eq1153 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1064 eq1155
    | exact resolve eq1155 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1161 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1158
       have r₂ := eq27
       grind)
    | exact resolve eq1158 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1168 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (σ y)) (σ (M.op x y)))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq1161 eq1122
    | exact resolve eq1122 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122 eq1161
  have eq1170 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1168 X0
       have i₂ := eq626 sF3 sF1
       grind)
    | (have i₁ := eq1168 X0
       have i₂ := eq626 X0 (M.op (M.op sF3 sF3) sF1)
       grind)
    | exact superpose eq626 eq1168
    | exact resolve eq1168 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1190 : (τ (σ x)) = (k x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1170 eq61
    | exact resolve eq61 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1170
  have eq1196 : (τ (σ x)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1041 eq1190
    | exact resolve eq1190 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1201 : x = (k x x) ∨ x = y := by
    first
    | exact superpose eq28 eq1196
    | exact resolve eq1196 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1196
  have eq1228 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq83 x x
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq83
    | (have j0 := eq83 x x
       grind)
    | exact resolve eq83 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1201
  have eq1229 : x = (M.op x x) ∨ x = y := by grind
  clear eq1228
  have eq1286 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq626 x X0
       have i₂ := eq1229
       grind)
    | exact superpose eq1229 eq626
    | exact resolve eq626 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1379 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq1286 y
       grind)
    | exact superpose eq1286 eq18
    | (have j1 := eq1286 y
       grind)
    | exact resolve eq18 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1286
  have eq1399 : x = y ∨ x = y := by
    first
    | exact superpose eq1041 eq1379
    | exact resolve eq1379 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq1379
  have eq1400 : x = y := by grind
  clear eq1399
  have eq1405 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1400
       grind)
    | exact superpose eq1400 eq24
    | exact resolve eq24 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1418 : ∀ X0 : G, (k X0 (M.op (M.op x x) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1117 X0
       have i₂ := eq1400
       grind)
    | exact superpose eq1400 eq1117
    | exact resolve eq1117 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117 eq1400
  have eq1421 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1418 X0
       have i₂ := eq626 x x
       grind)
    | (have i₁ := eq1418 X0
       have i₂ := eq626 X0 (M.op (M.op x x) x)
       grind)
    | exact superpose eq626 eq1418
    | exact resolve eq1418 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq1418
  have eq1428 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1405
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1405
    | exact resolve eq1405 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1405
  have eq1436 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1062 eq1428
    | exact resolve eq1428 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1467 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1436 eq1064
    | exact resolve eq1064 eq1436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq1436
  have eq3396 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1062 eq154
    | (have j0 := eq154 X0
       grind)
    | exact resolve eq154 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq3397 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3396 X0
       have i₂ := eq1421 X0
       grind)
    | exact superpose eq1421 eq3396
    | (have j0 := eq3396 X0
       grind)
    | exact resolve eq3396 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421 eq3396
  have eq3398 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1062 eq3397
    | (have j0 := eq3397 X0
       grind)
    | exact resolve eq3397 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq3397
  have eq3446 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3398
    | (have j0 := eq3398 (M.op x y)
       grind)
    | exact resolve eq3398 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3398
  have eq3455 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3446
  have eq3463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1467 eq3455
    | exact resolve eq3455 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq3455
  have eq3476 : False := by grind
  exact eq3476
