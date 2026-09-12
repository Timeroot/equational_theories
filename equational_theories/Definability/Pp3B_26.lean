import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_y_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X2))) ≠ X0 ∨ (M.op X1 (M.op X2 (M.op X0 X2))) = (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X1 (M.op X2 (M.op X0 X2)))) ∨ (M.op X1 (M.op X2 (M.op X0 X2))) = (k X1 (M.op X1 (M.op X2 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X1 (M.op X2 (M.op X0 X2)))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 (M.op X1 (M.op X2 (M.op X0 X2)))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq127 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  clear eq39
  have eq204 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq207 : x = (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op X1 X0)) (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : (σ x) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op X1 (σ x))) X0) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 (M.op X1 X0)) (M.op (σ y) (M.op (σ x) (σ y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X3 X2)) X4) = (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X2 X4 X3 (M.op X1 X2)
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X1 X3))) = (M.op (M.op X4 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 X4 (M.op X1 (M.op X2 (M.op X0 X2))) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y (M.op x y))) (M.op X1 (M.op X0 X1))) = (M.op (M.op X2 x) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op y X0))) = (M.op (M.op X1 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y X1 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y X1 x X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X0 (M.op X3 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 x X0 X1
       have i₂ := eq52 X2 x X0 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X1 X2)
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X0))) X3) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 (M.op X4 (M.op X2 X4))
       have i₂ := eq52 X2 X0 X1 X4
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) ≠ (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) ∨ (k X3 (M.op X1 (M.op X2 X1))) = (M.op X3 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X1 (M.op X2 X1))
       have i₂ := eq52 X2 X0 (M.op X1 (M.op X2 X1)) X1
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 X3 (M.op X1 (M.op X2 X1))
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op (M.op y (M.op x y)) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (M.op (M.op y sF0) (M.op X2 X0))
       have i₂ := eq52 X0 (M.op y sF0) X2 x
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op sF3 sF4) (M.op X2 X0))
       have i₂ := eq52 X0 (M.op sF3 sF4) X2 x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op (M.op X4 (M.op X5 X4)) (M.op X3 (M.op X0 (M.op X1 (M.op X2 X1)))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X3 (M.op X0 X2)) X4 X5 X3
       have i₂ := eq52 X2 X3 X0 X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 x))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq686 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq688 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq790 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) ≠ X2 ∨ (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op (M.op X0 (M.op X1 X2)) X0)) ∨ (M.op (M.op X0 (M.op X1 X2)) X0) = (k X1 (M.op (M.op X0 (M.op X1 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 X2 x
       have i₂ := eq52 X0 X1 X2 x
       grind)
    | exact superpose eq52 eq74
    | (have r₁ := eq74 (M.op X2 (M.op x (M.op X0 x))) (M.op (M.op X2 (M.op (M.op X2 (M.op x (M.op X0 x))) X2)) (M.op X2 X0)) X2
       have r₂ := eq52 X0 (M.op X2 (M.op (M.op X2 (M.op x (M.op X0 x))) X2)) X2 x
       grind)
    | exact resolve eq74 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq74
  have eq799 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X0 X2) X1)) (M.op X3 (M.op X0 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq503 X2 (M.op X1 (M.op (M.op X0 X2) X1)) X3
       have i₂ := eq503 X0 X2 X1
       grind)
    | exact superpose eq503 eq503
    | exact resolve eq503 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq503
    | exact resolve eq503 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq503
    | exact resolve eq503 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq816 eq503
    | exact resolve eq503 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X2) X3)) = (M.op (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq508 X1 X2 (M.op X3 (M.op (M.op X0 X2) X3))
       have i₂ := eq503 X0 X2 X3
       grind)
    | exact superpose eq503 eq508
    | exact resolve eq508 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq508 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq508
    | (have j0 := eq508 X0 x y
       grind)
    | exact resolve eq508 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq508
    | (have j0 := eq508 X0 (σ x) (σ y)
       grind)
    | exact resolve eq508 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op X0 (σ x)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq213 eq508
    | exact resolve eq508 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq975 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq840 eq14
    | exact resolve eq14 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq503 X0 y X0
       have i₂ := eq975 X0
       grind)
    | (have i₁ := eq503 x y x
       have i₂ := eq975 X0
       grind)
    | exact superpose eq975 eq503
    | exact resolve eq503 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op (M.op X0 (M.op x y)) X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq875 eq814
    | exact resolve eq814 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq1236 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq879 eq814
    | exact resolve eq814 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1296 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X2 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq814 X1 X2 X0
       grind)
    | exact superpose eq814 eq503
    | exact resolve eq503 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1018 (M.op x (M.op x x))
       have i₂ := eq814 x x sF0
       grind)
    | exact superpose eq814 eq1018
    | exact resolve eq1018 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1318 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq26 eq1236
    | (have j0 := eq1236 X0 X1
       grind)
    | exact resolve eq1236 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1319 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op (M.op X0 (M.op x y)) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1235 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1235
    | (have j0 := eq1235 X0 X1
       grind)
    | exact resolve eq1235 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1355 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op x (M.op (M.op X0 (σ x)) (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq51 eq210
    | exact resolve eq210 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq210
  have eq1723 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op x (M.op (M.op X0 (σ x)) (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq50 eq215
    | exact resolve eq215 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1885 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op (σ x) (M.op (M.op X0 x) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq50 eq216
    | exact resolve eq216 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1922 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq216 eq508
    | exact resolve eq508 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq2837 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X2 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq1296 X1 X2 X0
       grind)
    | exact superpose eq1296 eq503
    | exact resolve eq503 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2853 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq814 (M.op (M.op X1 X0) X1) (M.op X1 X0) X2
       have i₂ := eq1296 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq1296 eq814
    | exact resolve eq814 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2913 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1318 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq814 X0 X1 (M.op X0 sF4)
       grind)
    | exact superpose eq814 eq1318
    | exact resolve eq1318 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq3019 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1319 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq814 X0 X1 (M.op X0 sF0)
       grind)
    | exact superpose eq814 eq1319
    | exact resolve eq1319 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq6790 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq506 (M.op x sF4)
       have i₂ := eq504 (M.op x sF4) sF4 x x
       grind)
    | (have i₁ := eq506 (M.op x sF4)
       have i₂ := eq504 (M.op x sF4) X1 x sF4
       grind)
    | exact superpose eq504 eq506
    | exact resolve eq506 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq506
  have eq7739 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op (M.op X1 x) X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq50 eq509
    | exact resolve eq509 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq8888 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq688 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq688
    | (have j0 := eq688 (τ X0)
       grind)
    | exact resolve eq688 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq8896 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8888 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8888
    | (have j0 := eq8888 X0
       grind)
    | exact resolve eq8888 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8888
  have eq8902 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8896 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8896
    | (have j0 := eq8896 X0
       grind)
    | exact resolve eq8896 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8896
  have eq10154 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op y (M.op x y))) = (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op (M.op (M.op X0 x) X0) X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq494 eq503
    | exact resolve eq503 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq503
  have eq10243 : ∀ X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) x) = (M.op X2 (M.op y (M.op x y))) := by
    intro X1 X2
    first
    | (have i₁ := eq10154 x X1 X2 x
       have i₂ := eq2837 x x x
       grind)
    | exact superpose eq2837 eq10154
    | exact resolve eq10154 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10154
  have eq16433 : ∀ X1 X2 : G, x = (M.op y (M.op (M.op X1 (M.op (M.op X2 (M.op x y)) X2)) X1)) := by
    intro X1 X2
    first
    | exact superpose eq50 eq485
    | exact resolve eq485 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq485
  have eq17606 : ∀ X0 X2 X3 : G, (M.op (M.op X3 y) X3) = (M.op (M.op (M.op X0 (M.op x y)) X0) (M.op X2 (M.op x X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq492 y x x X2 X3
       have i₂ := eq496 x X0
       grind)
    | exact superpose eq496 eq492
    | exact resolve eq492 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq17941 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op y (M.op x y)) (M.op (M.op X2 (M.op X3 (M.op X1 X3))) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq522 (M.op X2 (M.op X3 (M.op X1 X3))) x X2
       have i₂ := eq492 X1 X2 X3 x X0
       grind)
    | exact superpose eq492 eq522
    | exact resolve eq522 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq17942 : ∀ X0 X1 X2 X3 : G, (σ x) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op X2 (M.op X3 (M.op X1 X3))) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq523 (M.op X2 (M.op X3 (M.op X1 X3))) x X2
       have i₂ := eq492 X1 X2 X3 x X0
       grind)
    | exact superpose eq492 eq523
    | exact resolve eq523 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq523
  have eq18202 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17942 X0 X1 x x
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq17942
    | exact resolve eq17942 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17942
  have eq18203 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op y (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17941 X0 X1 x x
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq17941
    | exact resolve eq17941 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17941
  have eq18284 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) (M.op y (M.op x y))) = (M.op (M.op X3 y) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq17606 X0 x X3
       have i₂ := eq1304 x
       grind)
    | (have i₁ := eq17606 X0 y X3
       have i₂ := eq1304 X0
       grind)
    | exact superpose eq1304 eq17606
    | (have j0 := eq17606 X0 y X3
       grind)
    | exact resolve eq17606 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17606
  have eq18366 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 (M.op x y)) X0) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq18284 X0 x
       have i₂ := eq975 x
       grind)
    | (have i₁ := eq18284 X0 x
       have i₂ := eq975 X0
       grind)
    | exact superpose eq975 eq18284
    | (have j0 := eq18284 X0 x
       grind)
    | exact resolve eq18284 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq18284
  have eq20104 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x (M.op X1 X0)) (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq559 eq511
    | exact resolve eq511 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq25405 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167
    | (have j0 := eq167 x
       grind)
    | exact resolve eq167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq25475 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25405
  have eq25493 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25475
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq25475
    | exact resolve eq25475 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25475
  have eq25503 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq25493
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq25493 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25493
  have eq25509 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq25503 eq49
    | exact resolve eq49 eq25503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq25889 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq204
    | (have j0 := eq204 (M.op x y)
       grind)
    | exact resolve eq204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq25956 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq25889
  have eq25959 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq129 eq25956
    | exact resolve eq25956 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq25956
  have eq25971 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq25959
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq25959 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25959
  have eq25979 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq25971 eq152
    | exact resolve eq152 eq25971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq25971
  have eq63666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq63666
    | exact resolve eq63666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63666
  have eq63685 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq63674
       have r₂ := eq27
       grind)
    | exact resolve eq63674 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63674
  have eq63687 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq63685
    | exact resolve eq63685 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63685
  have eq63689 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq63687 eq25509
    | exact resolve eq25509 eq63687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63687
  have eq63839 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq63689
    | exact resolve eq63689 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63689
  have eq63851 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq8902 x
       grind)
    | (have r₁ := eq63839
       have r₂ := eq8902 x
       grind)
    | exact resolve eq63839 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63839
  have eq63862 : y = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq840 x
       have i₂ := eq63851
       grind)
    | exact superpose eq63851 eq840
    | exact resolve eq840 eq63851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq63864 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq63851
       grind)
    | exact superpose eq63851 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq63851
       grind)
    | exact resolve eq13 eq63851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63957 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq63864 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63864
  have eq64015 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63862
       have i₂ := eq63851
       grind)
    | exact superpose eq63851 eq63862
    | exact resolve eq63862 eq63851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63862
  have eq64136 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64015
  have eq64328 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op (M.op X0 (M.op X1 X0)) y)) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq64136 eq559
    | exact resolve eq559 eq64136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq64513 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq64328 X0 X1
       have i₂ := eq814 y sF0 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq814 eq64328
    | exact resolve eq64328 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64328
  have eq65564 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq63957 x
       grind)
    | exact superpose eq63957 eq43
    | exact resolve eq43 eq63957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq65578 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq63957 sF0
       grind)
    | exact superpose eq63957 eq127
    | exact resolve eq127 eq63957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq63957
  have eq65625 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25503 eq65564
    | exact resolve eq65564 eq25503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25503 eq65564
  have eq101980 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64136 eq65578
    | exact resolve eq65578 eq64136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64136 eq65578
  have eq102037 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq101980
  have eq102041 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102037
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102037
    | exact resolve eq102037 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102037
  have eq102149 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65625
       have i₂ := eq63851
       grind)
    | exact superpose eq63851 eq65625
    | exact resolve eq65625 eq63851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63851 eq65625
  have eq102206 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq102149
  have eq102208 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102206
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102206
    | exact resolve eq102206 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102206
  have eq102226 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq102208 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq102208
       grind)
    | exact resolve eq13 eq102208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102208
  have eq102339 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq102226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102226
  have eq102938 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102339 eq102041
    | exact resolve eq102041 eq102339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102041 eq102339
  have eq102976 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq102938
  have eq103105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102976 eq64513
    | exact resolve eq64513 eq102976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64513 eq102976
  have eq103108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq103105
  have eq103109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq103108
    | exact resolve eq103108 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103108
  have eq103204 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq103109
       have r₂ := eq27
       grind)
    | exact resolve eq103109 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103109
  have eq103234 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103204 eq27
    | exact resolve eq27 eq103204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103236 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103204 eq73
    | (have r₁ := eq73
       have r₂ := eq103204
       grind)
    | exact resolve eq73 eq103204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq103309 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op (M.op X0 (σ x)) (M.op X1 (M.op X0 X1)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq103204 eq6790
    | exact resolve eq6790 eq103204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6790 eq103204
  have eq103324 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq103236
  have eq103325 : (σ x) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1922 eq103309
    | exact resolve eq103309 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922 eq103309
  have eq104515 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq103325 eq2853
    | exact resolve eq2853 eq103325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2853 eq103325
  have eq104551 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq104515
    | (have j0 := eq104515 X0
       grind)
    | exact resolve eq104515 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104515
  have eq159975 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103324 eq110
    | exact resolve eq110 eq103324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq103324
  have eq159997 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq159975
  have eq160008 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq159997
       have r₂ := eq103234
       grind)
    | exact resolve eq159997 eq103234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103234 eq159997
  have eq160039 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq160008 eq25509
    | exact resolve eq25509 eq160008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160008
  have eq160274 : x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq160039
    | exact resolve eq160039 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq160039
  have eq160295 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq8902 x
       grind)
    | (have r₁ := eq160274
       have r₂ := eq8902 x
       grind)
    | exact resolve eq160274 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160274
  have eq160313 : (M.op y (M.op x y)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1304 x
       have i₂ := eq160295
       grind)
    | exact superpose eq160295 eq1304
    | exact resolve eq1304 eq160295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160328 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq160295
       grind)
    | exact superpose eq160295 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq160295
       grind)
    | exact resolve eq13 eq160295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160295
  have eq160446 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq160328 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160328
  have eq160734 : y = (M.op (M.op x y) (M.op (M.op x (M.op x x)) (M.op x x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq160313 eq20104
    | exact resolve eq20104 eq160313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160313
  have eq160751 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq160734
       have i₂ := eq814 x x x
       grind)
    | exact superpose eq814 eq160734
    | exact resolve eq160734 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160734
  have eq160948 : (σ x) = (M.op (M.op y (M.op x y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq160751 eq18202
    | exact resolve eq18202 eq160751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18202
  have eq160949 : x = (M.op (M.op y (M.op x y)) (M.op (M.op y (M.op x y)) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq160751 eq18203
    | exact resolve eq18203 eq160751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18203 eq160751
  have eq160967 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq816 eq160949
    | exact resolve eq160949 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160949
  have eq160968 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq816 eq160948
    | exact resolve eq160948 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160948
  have eq161561 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq160968 eq104551
    | exact resolve eq104551 eq160968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104551 eq160968
  have eq161694 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq161561
  have eq163187 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq161694 eq25509
    | exact resolve eq25509 eq161694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25509 eq161694
  have eq163483 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq163187
    | exact resolve eq163187 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq163187
  have eq167848 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq163483
       have i₂ := eq160446 x
       grind)
    | exact superpose eq160446 eq163483
    | exact resolve eq163483 eq160446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160446 eq163483
  have eq167901 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq167848
  have eq167955 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1304 x
       have i₂ := eq167901
       grind)
    | exact superpose eq167901 eq1304
    | exact resolve eq1304 eq167901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167901
  have eq168203 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq167955
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq167955
    | exact resolve eq167955 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq167955
  have eq169045 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq168203 eq160967
    | exact resolve eq160967 eq168203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160967 eq168203
  have eq169192 : x = (M.op x y) := by grind
  clear eq169045
  have eq169719 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq169192 eq20
    | exact resolve eq20 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq169870 : ∀ X0 X1 : G, x = (M.op y (M.op (M.op X0 (M.op (M.op X1 x) X1)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq169192 eq16433
    | exact resolve eq16433 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16433
  have eq169903 : x = (M.op y (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq169870 x x
       have i₂ := eq7739 x x
       grind)
    | exact superpose eq7739 eq169870
    | exact resolve eq169870 eq7739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169870
  have eq169961 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq169719
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq169719
    | exact resolve eq169719 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169719
  have eq169962 : x = (M.op y (M.op y x)) := by
    first
    | exact superpose eq169192 eq169903
    | exact resolve eq169903 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169903
  have eq174039 : ∀ X0 X1 : G, (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (M.op (M.op X0 (M.op x X0)) (M.op X1 (M.op x X1))) := by
    intro X0 X1
    first
    | exact superpose eq207 eq799
    | exact resolve eq799 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq799
  have eq176180 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (M.op (M.op X0 (M.op x X0)) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq174039 X0 x
       have i₂ := eq1304 x
       grind)
    | (have i₁ := eq174039 X0 y
       have i₂ := eq1304 X0
       grind)
    | exact superpose eq1304 eq174039
    | (have j0 := eq174039 X0 y
       grind)
    | exact resolve eq174039 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174039
  have eq176540 : ∀ X0 : G, (M.op (M.op y x) (M.op y x)) = (M.op (M.op X0 (M.op x X0)) (M.op y x)) := by
    intro X0
    first
    | exact superpose eq169192 eq176180
    | exact resolve eq176180 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176180
  have eq176663 : y = (M.op (M.op y x) (M.op y x)) := by
    first
    | (have i₁ := eq176540 x
       have i₂ := eq814 x x y
       grind)
    | exact superpose eq814 eq176540
    | exact resolve eq176540 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq176540
  have eq177050 : x ≠ (M.op y (M.op y x)) ∨ (M.op y (M.op y x)) = (M.op (M.op y (M.op y x)) (M.op y (M.op y x))) ∨ (M.op y (M.op y x)) = (k y (M.op y (M.op y x))) := by
    first
    | (have i₁ := eq790 (M.op y x) y x
       have i₂ := eq176663
       grind)
    | exact superpose eq176663 eq790
    | exact resolve eq790 eq176663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq176663
  have eq177257 : (M.op y (M.op y x)) = (M.op (M.op y (M.op y x)) (M.op y (M.op y x))) ∨ (M.op y (M.op y x)) = (k y (M.op y (M.op y x))) := by
    first
    | (have r₁ := eq177050
       have r₂ := eq169962
       grind)
    | exact resolve eq177050 eq169962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177050
  have eq177318 : x = (M.op x x) ∨ (M.op y (M.op y x)) = (k y (M.op y (M.op y x))) := by
    first
    | (have i₁ := eq177257
       have i₂ := eq169962
       grind)
    | exact superpose eq169962 eq177257
    | exact resolve eq177257 eq169962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177257
  have eq177352 : x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq177318
       have i₂ := eq169962
       grind)
    | exact superpose eq169962 eq177318
    | exact resolve eq177318 eq169962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169962 eq177318
  have eq191755 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op X2 (M.op (M.op X1 (M.op x y)) X1)) X2) (M.op y (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq18366 eq865
    | exact resolve eq865 eq18366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq18366
  have eq195761 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op (M.op X2 (M.op (M.op X1 x) X1)) X2) (M.op y x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq169192 eq191755
    | exact resolve eq191755 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191755
  have eq196181 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y (M.op x y)) (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq195761 X0 x x
       have i₂ := eq7739 x x
       grind)
    | exact superpose eq7739 eq195761
    | exact resolve eq195761 eq7739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7739 eq195761
  have eq196333 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x x) X0)) := by
    intro X0
    first
    | exact superpose eq816 eq196181
    | exact resolve eq196181 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq196181
  have eq206005 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op X0 (σ (M.op x y))) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq169961 eq880
    | exact resolve eq880 eq169961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq223231 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op x (M.op (M.op X0 (σ x)) (M.op y x))) := by
    intro X0
    first
    | exact superpose eq169192 eq1355
    | exact resolve eq1355 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq223232 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op x (M.op (M.op X0 (σ (M.op x y))) (M.op y x))) := by
    intro X0
    first
    | exact superpose eq169961 eq223231
    | exact resolve eq223231 eq169961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223231
  have eq224160 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq686 x y
       have i₂ := eq177352
       grind)
    | exact superpose eq177352 eq686
    | (have j0 := eq686 x y
       grind)
    | exact resolve eq686 eq177352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq177352
  have eq224162 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq224160
  have eq224166 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq224162
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq224162
    | exact resolve eq224162 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224162
  have eq224184 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq224166
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq224166
    | exact resolve eq224166 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224166
  have eq224200 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq224184
    | exact resolve eq224184 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq224184
  have eq224216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq169961 eq224200
    | exact resolve eq224200 eq169961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224200
  have eq224226 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq224216
       have r₂ := eq27
       grind)
    | exact resolve eq224216 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224216
  have eq224233 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq224226
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq224226
    | exact resolve eq224226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224226
  have eq224240 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq169961 eq224233
    | exact resolve eq224233 eq169961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224233
  have eq225706 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq224240 eq25979
    | exact resolve eq25979 eq224240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25979 eq224240
  have eq225914 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq169192 eq225706
    | exact resolve eq225706 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225706
  have eq225936 : (M.op x y) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq225914
    | exact resolve eq225914 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq225914
  have eq225946 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq169192 eq225936
    | exact resolve eq225936 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225936
  have eq225950 : x = (M.op x x) := by
    first
    | (have j1 := eq8902 x
       grind)
    | (have r₁ := eq225946
       have r₂ := eq8902 x
       grind)
    | exact resolve eq225946 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8902 eq225946
  have eq226102 : ∀ X0 : G, x = (M.op X0 (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq2837 X0 x x
       have i₂ := eq225950
       grind)
    | exact superpose eq225950 eq2837
    | exact resolve eq2837 eq225950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837
  have eq226147 : x = y := by
    first
    | (have i₁ := eq226102 x
       have i₂ := eq196333 x
       grind)
    | exact superpose eq196333 eq226102
    | exact resolve eq226102 eq196333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196333 eq226102
  have eq226505 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq226147
       grind)
    | exact superpose eq226147 eq24
    | exact resolve eq24 eq226147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq226868 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq226505
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq226505
    | exact resolve eq226505 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226505
  have eq227024 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq169961 eq226868
    | exact resolve eq226868 eq169961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226868
  have eq228704 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op x (M.op (M.op X0 (σ x)) (M.op y x))) := by
    intro X0
    first
    | exact superpose eq169192 eq1723
    | exact resolve eq1723 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq228705 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op x (M.op (M.op X0 (σ x)) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq228704 X0
       have i₂ := eq226147
       grind)
    | exact superpose eq226147 eq228704
    | exact resolve eq228704 eq226147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228704
  have eq228706 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op x (M.op (M.op X0 (σ x)) x)) := by
    intro X0
    first
    | (have i₁ := eq228705 X0
       have i₂ := eq225950
       grind)
    | exact superpose eq225950 eq228705
    | exact resolve eq228705 eq225950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228705
  have eq228707 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op x (M.op (M.op X0 (σ (M.op x y))) x)) := by
    intro X0
    first
    | exact superpose eq169961 eq228706
    | exact resolve eq228706 eq169961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228706
  have eq228875 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op X1 (M.op X2 X1)) (M.op x (M.op (M.op X0 (σ (M.op x y))) (M.op X3 (M.op x X3)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq228707 eq558
    | exact resolve eq558 eq228707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq228707
  have eq229109 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op X1 (M.op X2 X1)) (M.op x (M.op (M.op X0 (σ (M.op x y))) (M.op y (M.op x y)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq228875 X0 X1 X2 x
       have i₂ := eq1304 x
       grind)
    | (have i₁ := eq228875 X0 X1 X2 y
       have i₂ := eq1304 X0
       grind)
    | exact superpose eq1304 eq228875
    | (have j0 := eq228875 X0 X1 X2 y
       grind)
    | exact resolve eq228875 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228875
  have eq229247 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op X1 (M.op X2 X1)) (M.op x (M.op (M.op X0 (σ (M.op x y))) (M.op y x))))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq169192 eq229109
    | exact resolve eq229109 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229109
  have eq229355 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq223232 eq229247
    | exact resolve eq229247 eq223232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223232 eq229247
  have eq229444 : ∀ X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (M.op X2 X1)) (M.op (σ x) (σ y)))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq229355 x X1 X2
       have i₂ := eq2913 (M.op X1 (M.op X2 X1)) (M.op x (M.op sF3 sF4))
       grind)
    | exact superpose eq2913 eq229355
    | exact resolve eq229355 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913 eq229355
  have eq229481 : ∀ X1 X2 : G, (M.op (M.op x y) (M.op (M.op X1 (M.op X2 X1)) (M.op x y))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq229444 X1 X2
       have i₂ := eq3019 (M.op X1 (M.op X2 X1)) sF4
       grind)
    | exact superpose eq3019 eq229444
    | exact resolve eq229444 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019 eq229444
  have eq229509 : ∀ X1 X2 : G, (M.op x (M.op (M.op X1 (M.op X2 X1)) x)) = X2 := by
    intro X1 X2
    first
    | exact superpose eq169192 eq229481
    | exact resolve eq229481 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229481
  have eq229529 : ∀ X2 : G, (M.op x (M.op X2 (M.op y (M.op x y)))) = X2 := by
    intro X2
    first
    | (have i₁ := eq229509 x X2
       have i₂ := eq10243 x X2
       grind)
    | exact superpose eq10243 eq229509
    | exact resolve eq229509 eq10243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229509
  have eq229544 : ∀ X2 : G, (M.op x (M.op X2 (M.op y x))) = X2 := by
    intro X2
    first
    | exact superpose eq169192 eq229529
    | exact resolve eq229529 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229529
  have eq229552 : ∀ X2 : G, (M.op x (M.op X2 (M.op x x))) = X2 := by
    intro X2
    first
    | (have i₁ := eq229544 X2
       have i₂ := eq226147
       grind)
    | exact superpose eq226147 eq229544
    | exact resolve eq229544 eq226147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229544
  have eq229559 : ∀ X2 : G, (M.op x (M.op X2 x)) = X2 := by
    intro X2
    first
    | (have i₁ := eq229552 X2
       have i₂ := eq225950
       grind)
    | exact superpose eq225950 eq229552
    | exact resolve eq229552 eq225950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229552
  have eq230621 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op (σ x) (M.op (M.op X0 x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq227024 eq1885
    | exact resolve eq1885 eq227024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq230622 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op X0 x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq169961 eq230621
    | exact resolve eq230621 eq169961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230621
  have eq230623 : ∀ X0 : G, (M.op X0 (M.op y x)) = (M.op (σ (M.op x y)) (M.op (M.op X0 x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq169192 eq230622
    | exact resolve eq230622 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230622
  have eq230624 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op (σ (M.op x y)) (M.op (M.op X0 x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq230623 X0
       have i₂ := eq226147
       grind)
    | exact superpose eq226147 eq230623
    | exact resolve eq230623 eq226147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230623
  have eq230625 : ∀ X0 : G, (M.op X0 x) = (M.op (σ (M.op x y)) (M.op (M.op X0 x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq230624 X0
       have i₂ := eq225950
       grind)
    | exact superpose eq225950 eq230624
    | exact resolve eq230624 eq225950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230624
  have eq230876 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) (M.op (M.op x (M.op X0 x)) (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq230625 eq20104
    | exact resolve eq20104 eq230625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20104 eq230625
  have eq230885 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) (M.op (M.op x (M.op X0 x)) (M.op y x))) := by
    intro X0
    first
    | exact superpose eq169192 eq230876
    | exact resolve eq230876 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230876
  have eq231037 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) (M.op (M.op x (M.op X0 x)) (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq230885 X0
       have i₂ := eq226147
       grind)
    | exact superpose eq226147 eq230885
    | exact resolve eq230885 eq226147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230885
  have eq231169 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) (M.op (M.op x (M.op X0 x)) x)) := by
    intro X0
    first
    | (have i₁ := eq231037 X0
       have i₂ := eq225950
       grind)
    | exact superpose eq225950 eq231037
    | exact resolve eq231037 eq225950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231037
  have eq231290 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq231169 x
       have i₂ := eq1296 x (M.op x x) (M.op sF1 sF4)
       grind)
    | exact superpose eq1296 eq231169
    | exact resolve eq231169 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296 eq231169
  have eq231499 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ (M.op x y))) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq231290 eq508
    | exact resolve eq508 eq231290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq231636 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq206005 eq231499
    | exact resolve eq231499 eq206005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206005 eq231499
  have eq231697 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq227024 eq231636
    | exact resolve eq231636 eq227024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227024 eq231636
  have eq231752 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq231290 eq231697
    | exact resolve eq231697 eq231290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231290 eq231697
  have eq236418 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) ≠ (M.op (M.op X0 (M.op x X0)) x) ∨ (M.op X1 (M.op X0 (M.op x X0))) = (k X1 (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq512 x X0 x X1
       have i₂ := eq229559 (M.op X0 (M.op x X0))
       grind)
    | exact superpose eq229559 eq512
    | (have j0 := eq512 X0 X0 x X1
       grind)
    | exact resolve eq512 eq229559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq236749 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) ≠ (M.op x (M.op y (M.op x y))) ∨ (M.op X1 (M.op X0 (M.op x X0))) = (k X1 (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq236418 X0 X1
       have i₂ := eq10243 X0 x
       grind)
    | exact superpose eq10243 eq236418
    | (have j0 := eq236418 X0 X1
       grind)
    | exact resolve eq236418 eq10243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10243 eq236418
  have eq236981 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) ≠ (M.op x (M.op y x)) ∨ (M.op X1 (M.op X0 (M.op x X0))) = (k X1 (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | exact superpose eq169192 eq236749
    | (have j0 := eq236749 X0 X1
       grind)
    | exact resolve eq236749 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236749
  have eq237169 : ∀ X0 X1 : G, y ≠ (M.op X0 (M.op x X0)) ∨ (M.op X1 (M.op X0 (M.op x X0))) = (k X1 (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq236981 X0 X1
       have i₂ := eq229559 y
       grind)
    | (have i₁ := eq236981 X0 X1
       have i₂ := eq229559 (M.op x (M.op y x))
       grind)
    | exact superpose eq229559 eq236981
    | (have j0 := eq236981 X0 X1
       grind)
    | exact resolve eq236981 eq229559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229559 eq236981
  have eq237297 : ∀ X0 X1 : G, y ≠ (M.op y (M.op x y)) ∨ (M.op X1 (M.op X0 (M.op x X0))) = (k X1 (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq237169 X0 X1
       have i₂ := eq1304 X0
       grind)
    | (have i₁ := eq237169 y X1
       have i₂ := eq1304 X0
       grind)
    | exact superpose eq1304 eq237169
    | (have j0 := eq237169 y X1
       grind)
    | exact resolve eq237169 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237169
  have eq237358 : ∀ X0 X1 : G, y ≠ (M.op y x) ∨ (M.op X1 (M.op X0 (M.op x X0))) = (k X1 (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | exact superpose eq169192 eq237297
    | (have j0 := eq237297 X0 X1
       grind)
    | exact resolve eq237297 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237297
  have eq237393 : ∀ X0 X1 : G, x ≠ (M.op x x) ∨ (M.op X1 (M.op X0 (M.op x X0))) = (k X1 (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq237358 X0 X1
       have i₂ := eq226147
       grind)
    | exact superpose eq226147 eq237358
    | (have j0 := eq237358 X0 X1
       grind)
    | exact resolve eq237358 eq226147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237358
  have eq237409 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x X0))) = (k X1 (M.op X0 (M.op x X0))) := by
    intro X0 X1
    first
    | (have j0 := eq237393 X0 X1
       grind)
    | (have r₁ := eq237393 X0 X1
       have r₂ := eq225950
       grind)
    | exact resolve eq237393 eq225950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237393
  have eq237415 : ∀ X1 : G, (M.op X1 (M.op y (M.op x y))) = (k X1 (M.op y (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq237409 y X1
       have i₂ := eq1304 x
       grind)
    | (have i₁ := eq237409 x X1
       have i₂ := eq1304 x
       grind)
    | exact superpose eq1304 eq237409
    | (have j0 := eq237409 y X1
       grind)
    | exact resolve eq237409 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq237409
  have eq237418 : ∀ X1 : G, (M.op X1 (M.op y x)) = (k X1 (M.op y x)) := by
    intro X1
    first
    | exact superpose eq169192 eq237415
    | exact resolve eq237415 eq169192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169192 eq237415
  have eq237421 : ∀ X1 : G, (M.op X1 (M.op x x)) = (k X1 (M.op x x)) := by
    intro X1
    first
    | (have i₁ := eq237418 X1
       have i₂ := eq226147
       grind)
    | exact superpose eq226147 eq237418
    | exact resolve eq237418 eq226147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226147 eq237418
  have eq237424 : ∀ X1 : G, (M.op X1 x) = (k X1 x) := by
    intro X1
    first
    | (have i₁ := eq237421 X1
       have i₂ := eq225950
       grind)
    | exact superpose eq225950 eq237421
    | exact resolve eq237421 eq225950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237421
  have eq248414 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq688 x
       have i₂ := eq237424 x
       grind)
    | exact superpose eq237424 eq688
    | (have j0 := eq688 x
       grind)
    | exact resolve eq688 eq237424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq237424
  have eq248465 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq248414
       have i₂ := eq225950
       grind)
    | exact superpose eq225950 eq248414
    | exact resolve eq248414 eq225950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225950 eq248414
  have eq248466 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq248465
  have eq248531 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq248466
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq248466
    | exact resolve eq248466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq248466
  have eq248582 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq169961 eq248531
    | exact resolve eq248531 eq169961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169961 eq248531
  have eq248631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq231752 eq248582
    | exact resolve eq248582 eq231752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231752 eq248582
  have eq248676 : False := by grind
  exact eq248676

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxy_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq10
    | exact resolve eq10 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq75
    | exact resolve eq75 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq75
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq126 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq38
  have eq478 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq578 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq631 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 x))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq974 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq578 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq578
    | exact resolve eq578 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq578
    | exact resolve eq578 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq997 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq976 eq578
    | exact resolve eq578 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq976
  have eq59384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq59385 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq59384
    | exact resolve eq59384 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59384
  have eq59395 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq59385
       have r₂ := eq28
       grind)
    | exact resolve eq59385 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59385
  have eq59398 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq59395 eq78
    | exact resolve eq78 eq59395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59395
  have eq59557 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq59398
    | exact resolve eq59398 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59398
  have eq59558 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59557
  have eq59582 : y = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq997 x
       have i₂ := eq59558
       grind)
    | exact superpose eq59558 eq997
    | exact resolve eq997 eq59558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq59584 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq59558
       grind)
    | exact superpose eq59558 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq59558
       grind)
    | exact resolve eq13 eq59558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59586 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq478 x X0
       have i₂ := eq59558
       grind)
    | exact superpose eq59558 eq478
    | (have j0 := eq478 x X0
       grind)
    | exact resolve eq478 eq59558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq59676 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59586
  have eq59677 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59584
  have eq59720 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq59676 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq59676
    | (have j0 := eq59676 X0
       grind)
    | exact resolve eq59676 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59676
  have eq60044 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59582
       have i₂ := eq59558
       grind)
    | exact superpose eq59558 eq59582
    | exact resolve eq59582 eq59558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59558 eq59582
  have eq60152 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq60044
  have eq60215 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op (M.op X0 (M.op X1 X0)) y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq60152 eq631
    | exact resolve eq631 eq60152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq60382 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq60215 X0 X1
       have i₂ := eq974 y sF0 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq974 eq60215
    | exact resolve eq60215 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq60215
  have eq61378 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq126
       have i₂ := eq59677 sF0
       grind)
    | exact superpose eq59677 eq126
    | exact resolve eq126 eq59677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq59677
  have eq99321 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq60152 eq61378
    | exact resolve eq61378 eq60152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60152 eq61378
  have eq99388 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq99321
  have eq99394 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq99388
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq99388
    | exact resolve eq99388 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99388
  have eq100003 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq99394 eq59720
    | exact resolve eq59720 eq99394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59720 eq99394
  have eq100010 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq100003
  have eq100134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq100010 eq60382
    | exact resolve eq60382 eq100010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60382 eq100010
  have eq100137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq100134
  have eq100138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq100137
    | exact resolve eq100137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100137
  have eq100226 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq100138
       have r₂ := eq28
       grind)
    | exact resolve eq100138 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100138
  have eq100241 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq100226 eq30
    | exact resolve eq30 eq100226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq100226
  have eq100431 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq100241
    | exact resolve eq100241 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq100241
  have eq100432 : x = y := by grind
  clear eq100431
  have eq100445 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq100432
       grind)
    | exact superpose eq100432 eq19
    | exact resolve eq19 eq100432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq100446 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq100432
       grind)
    | exact superpose eq100432 eq25
    | exact resolve eq25 eq100432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq100432
  have eq100651 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq100446
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq100446
    | exact resolve eq100446 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq100446
  have eq100675 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq100651 eq27
    | exact resolve eq27 eq100651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq100651
  have eq101218 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq100675 eq78
    | exact resolve eq78 eq100675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq100675
  have eq101434 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101218
       have i₂ := eq100445
       grind)
    | exact superpose eq100445 eq101218
    | exact resolve eq101218 eq100445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100445 eq101218
  have eq101489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq101434 eq15
    | exact resolve eq15 eq101434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101434
  have eq101565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq101489
    | exact resolve eq101489 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq101489
  have eq101586 : False := by grind
  exact eq101586

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq10
    | exact resolve eq10 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq75
    | exact resolve eq75 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq87 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq73 sF3
       grind)
    | exact superpose eq73 eq71
    | exact resolve eq71 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq73 y
       grind)
    | exact superpose eq73 eq87
    | exact resolve eq87 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq87
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq128 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq38
  have eq478 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq578 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X3 (M.op X1 X2) X2 X4
       have i₂ := eq53 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq974 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq578 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq578
    | exact resolve eq578 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq578
    | exact resolve eq578 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq997 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq976 eq578
    | exact resolve eq578 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1026 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq997 eq14
    | exact resolve eq14 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1405 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq974 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq974
    | (have j0 := eq974 y X0 x
       grind)
    | exact resolve eq974 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1420 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq578 X2 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq974 X1 X2 X0
       grind)
    | exact superpose eq974 eq578
    | exact resolve eq578 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1450 : ∀ X0 : G, (M.op (M.op y X0) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq1405 eq578
    | exact resolve eq578 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2887 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq578 X2 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq1420 X1 X2 X0
       grind)
    | exact superpose eq1420 eq578
    | exact resolve eq578 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq1420
  have eq59403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq59404 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq59403
    | exact resolve eq59403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59403
  have eq59415 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq59404
       have r₂ := eq28
       grind)
    | exact resolve eq59404 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59404
  have eq59419 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq59415 eq113
    | exact resolve eq113 eq59415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq59415
  have eq59554 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq59419
    | exact resolve eq59419 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59419
  have eq59555 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59554
  have eq59575 : y = (M.op y (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1450 y
       have i₂ := eq59555
       grind)
    | exact superpose eq59555 eq1450
    | exact resolve eq1450 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq59576 : x = (M.op (M.op y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1405 y
       have i₂ := eq59555
       grind)
    | exact superpose eq59555 eq1405
    | exact resolve eq1405 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq59577 : (M.op y y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1026 y
       have i₂ := eq59555
       grind)
    | exact superpose eq59555 eq1026
    | exact resolve eq1026 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq59578 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq59555
       grind)
    | exact superpose eq59555 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq59555
       grind)
    | exact resolve eq13 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59580 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq478 y X0
       have i₂ := eq59555
       grind)
    | exact superpose eq59555 eq478
    | (have j0 := eq478 y X0
       grind)
    | exact resolve eq478 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq59670 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59580 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59580
  have eq59671 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59578 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59578
  have eq59693 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq59670 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq59670
    | (have j0 := eq59670 X0
       grind)
    | exact resolve eq59670 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59670
  have eq60214 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59576
       have i₂ := eq59555
       grind)
    | exact superpose eq59555 eq59576
    | exact resolve eq59576 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59555 eq59576
  have eq60308 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq60214
  have eq61518 : y = (M.op y (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq59577 eq59575
    | exact resolve eq59575 eq59577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59575 eq59577
  have eq61614 : y = (M.op y (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq61518
  have eq61792 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq128
       have i₂ := eq59671 sF0
       grind)
    | exact superpose eq59671 eq128
    | exact resolve eq128 eq59671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq59671
  have eq63212 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) y)) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq626 X0 X1 X2 y y
       have i₂ := eq61614
       grind)
    | exact superpose eq61614 eq626
    | exact resolve eq626 eq61614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq61614
  have eq63429 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq63212 x X1 X2
       have i₂ := eq2887 y x (M.op (M.op X1 X2) X1)
       grind)
    | exact superpose eq2887 eq63212
    | exact resolve eq63212 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887 eq63212
  have eq96724 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq60308 eq61792
    | exact resolve eq61792 eq60308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60308 eq61792
  have eq96791 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq96724
  have eq96797 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq96791
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96791
    | exact resolve eq96791 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96791
  have eq96809 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq96797 eq59693
    | exact resolve eq59693 eq96797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59693 eq96797
  have eq96816 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq96809
  have eq96933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq96816 eq63429
    | exact resolve eq63429 eq96816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63429 eq96816
  have eq96934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq96933
  have eq96936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq96934
    | exact resolve eq96934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96934
  have eq96965 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq96936
       have r₂ := eq28
       grind)
    | exact resolve eq96936 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96936
  have eq96968 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq96965 eq30
    | exact resolve eq30 eq96965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq96965
  have eq97157 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq96968
    | exact resolve eq96968 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq96968
  have eq97158 : x = y := by grind
  clear eq97157
  have eq98125 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq97158
       grind)
    | exact superpose eq97158 eq19
    | exact resolve eq19 eq97158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq98126 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq97158
       grind)
    | exact superpose eq97158 eq25
    | exact resolve eq25 eq97158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq97158
  have eq98330 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq98126
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq98126
    | exact resolve eq98126 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq98126
  have eq98354 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98330 eq27
    | exact resolve eq27 eq98330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq98330
  have eq98889 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq98354 eq78
    | exact resolve eq78 eq98354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq98354
  have eq99099 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq98889
       have i₂ := eq98125
       grind)
    | exact superpose eq98125 eq98889
    | exact resolve eq98889 eq98125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98125 eq98889
  have eq99154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99099 eq15
    | exact resolve eq15 eq99099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99099
  have eq99230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq99154
    | exact resolve eq99154 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq99154
  have eq99251 : False := by grind
  exact eq99251

/-- `Equation2497`: `x = (y ◇ ((x ◇ x) ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation2497 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2497 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2497.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq137 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq139 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq140 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq140
    | (have j0 := eq140 X0 X1
       grind)
    | exact resolve eq140 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       have j1 := eq138 X1 X0
       grind)
    | (have r₁ := eq142 X1 X0
       have r₂ := eq138 X0 X1
       grind)
    | (have r₁ := eq142 (k X1 X0) X1
       have r₂ := eq138 X0 X1
       grind)
    | (have r₁ := eq142 X1 X1
       have r₂ := eq138 X1 X1
       grind)
    | exact resolve eq142 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq142
  have eq528 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq146
    | exact resolve eq146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq146 y x
       grind)
    | exact superpose eq146 eq16
    | (have j1 := eq146 y x
       grind)
    | exact resolve eq16 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq555 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq528
    | (have j0 := eq528 X0 X1
       grind)
    | exact resolve eq528 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq528
  have eq556 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq555
    | exact resolve eq555 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq617 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq556 (τ X1) X0
       grind)
    | exact superpose eq556 eq18
    | (have j1 := eq556 (τ X1) X0
       grind)
    | exact resolve eq18 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq556
  have eq806 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq617 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq617
    | exact resolve eq617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq858 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq806
    | (have j0 := eq806 X0 X1
       grind)
    | exact resolve eq806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq955 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq542
       have i₂ := eq858 y x
       grind)
    | exact superpose eq858 eq542
    | (have j1 := eq858 (σ y) (σ x)
       grind)
    | (have r₁ := eq542
       have r₂ := eq858 y x
       grind)
    | exact resolve eq542 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq955
  have eq990 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq956
  have eq994 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq542
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq542
    | exact resolve eq542 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq990
  have eq995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq994
  have eq996 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq995
  have eq1049 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq996
  have eq1054 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1049
    | exact resolve eq1049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1059 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1054
       grind)
    | exact superpose eq1054 eq16
    | exact resolve eq16 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1117 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1059
       have i₂ := eq858 y x
       grind)
    | exact superpose eq858 eq1059
    | (have j1 := eq858 y x
       grind)
    | (have r₁ := eq1059
       have r₂ := eq858 y x
       grind)
    | exact resolve eq1059 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq1118 : y = (M.op x x) := by grind
  clear eq1117
  have eq1124 : (M.op x y) = (k y x) := by grind
  clear eq1118
  have eq1197 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1059
       have i₂ := eq1124
       grind)
    | exact superpose eq1124 eq1059
    | exact resolve eq1059 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq1124
  have eq1200 : False := by grind
  exact eq1200

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_x_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq448 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq12
    | (have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq464 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq468 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq464
    | (have j0 := eq464 X0 X1
       grind)
    | exact resolve eq464 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq469 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq468 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq632 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq469
    | exact resolve eq469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq469 x y
       grind)
    | exact superpose eq469 eq16
    | (have j1 := eq469 x y
       grind)
    | exact resolve eq16 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq469 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq664 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq632
    | (have j0 := eq632 X0 X1
       grind)
    | exact resolve eq632 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq632
  have eq772 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq664 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq664
    | exact resolve eq664 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq827 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq772 (τ X0) X1
       grind)
    | exact superpose eq772 eq18
    | (have j1 := eq772 (τ X0) X1
       grind)
    | exact resolve eq18 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq772
  have eq1165 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq827 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq827
    | exact resolve eq827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq1221 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1165 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1165
    | (have j0 := eq1165 X0 X1
       grind)
    | exact resolve eq1165 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1334 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq639
       have i₂ := eq1221 x y
       grind)
    | exact superpose eq1221 eq639
    | (have j1 := eq1221 (σ x) (σ y)
       grind)
    | (have r₁ := eq639
       have r₂ := eq1221 x y
       grind)
    | exact resolve eq639 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq1335 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1334
  have eq1370 : y ≠ y ∨ y = (k y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1335
       grind)
    | exact superpose eq1335 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1335
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1335
       grind)
    | exact resolve eq13 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1375 : y = (M.op y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1370
  have eq3037 : y ≠ (M.op x y) ∨ y = (k y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1375
       grind)
    | exact superpose eq1375 eq12
    | exact resolve eq12 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq3045 : y ≠ (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3037
  have eq3049 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3045
       have r₂ := eq1335
       grind)
    | exact resolve eq3045 eq1335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335 eq3045
  have eq3054 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq656 x y
       have i₂ := eq3049
       grind)
    | exact superpose eq3049 eq656
    | (have j0 := eq656 x y
       grind)
    | exact resolve eq656 eq3049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq3049
  have eq3075 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3054
  have eq3076 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3075
  have eq3119 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3076
       grind)
    | exact superpose eq3076 eq16
    | exact resolve eq16 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3126 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3076
       grind)
    | exact superpose eq3076 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3076
       grind)
    | exact resolve eq13 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3132 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq3126
  have eq3133 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq3132
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3132
    | exact resolve eq3132 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132
  have eq3230 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3133
       grind)
    | exact superpose eq3133 eq12
    | exact resolve eq12 eq3133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133
  have eq3249 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq3230
       have r₂ := eq3076
       grind)
    | exact resolve eq3230 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3076 eq3230
  have eq3266 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq3249
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3249
    | exact resolve eq3249 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249
  have eq3267 : (σ y) = (σ (k y x)) := by grind
  clear eq3266
  have eq3322 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1221 x y
       have i₂ := eq3267
       grind)
    | exact superpose eq3267 eq1221
    | (have j0 := eq1221 x y
       grind)
    | exact resolve eq1221 eq3267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq3267
  have eq3397 : y = (M.op x y) := by
    first
    | (have r₁ := eq3322
       have r₂ := eq3119
       grind)
    | exact resolve eq3322 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322
  have eq3467 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3119
       have i₂ := eq3397
       grind)
    | exact superpose eq3397 eq3119
    | exact resolve eq3119 eq3397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119 eq3397
  have eq3477 : False := by grind
  exact eq3477

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq68
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq430 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq430
    | (have j0 := eq430 X0 X1
       grind)
    | exact resolve eq430 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq732 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq447
    | exact resolve eq447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq746 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq732
    | (have j0 := eq732 X0 X1
       grind)
    | exact resolve eq732 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq732
  have eq754 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq746 X0 X1
       have j1 := eq95 X1 X0
       grind)
    | (have r₁ := eq746 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq746 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq746 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq746
  have eq757 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq754 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq754
    | exact resolve eq754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq754 (σ X1) X0
       grind)
    | exact superpose eq754 eq15
    | (have j1 := eq754 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq807 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq757 (τ X0) X1
       grind)
    | exact superpose eq757 eq19
    | (have j1 := eq757 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq757
  have eq907 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq807 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq807
    | exact resolve eq807 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq948 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq907 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq907
    | (have j0 := eq907 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq907 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq1133 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq772 x y
       grind)
    | exact superpose eq772 eq16
    | (have j1 := eq772 x y
       grind)
    | exact resolve eq16 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq1149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1133
       have i₂ := eq948 x y
       grind)
    | exact superpose eq948 eq1133
    | (have j1 := eq948 (σ x) (σ y)
       grind)
    | (have r₁ := eq1133
       have r₂ := eq948 x y
       grind)
    | (have r₁ := eq1133
       have r₂ := eq948 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1133
       have r₂ := eq948 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1133 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq1133
  have eq1150 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1149
  have eq1153 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1150
       grind)
    | exact superpose eq1150 eq16
    | exact resolve eq16 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1154 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1153
       have r₂ := eq79 x
       grind)
    | exact resolve eq1153 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1155 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1154
       grind)
    | exact superpose eq1154 eq16
    | exact resolve eq16 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1156 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1154
       grind)
    | exact superpose eq1154 eq10
    | exact resolve eq10 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1201 : x = y := by
    first
    | (have i₁ := eq1156
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1156
    | exact resolve eq1156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1202 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1155
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq1155
    | exact resolve eq1155 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1155
  have eq1203 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1202
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq1202
    | exact resolve eq1202 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq1202
  have eq1204 : False := by grind
  exact eq1204

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation2533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq328 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq354 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq328
    | (have j0 := eq328 X0 X1
       grind)
    | exact resolve eq328 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq328
  have eq359 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq354 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq354 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq354 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq354 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq362 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq359
    | (have j0 := eq359 X0 X1
       grind)
    | exact resolve eq359 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq359
  have eq425 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq362
    | exact resolve eq362 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq362 (σ X0) X1
       grind)
    | exact superpose eq362 eq15
    | (have j1 := eq362 (σ X0) X1
       grind)
    | exact resolve eq15 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq454 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq435
    | (have j0 := eq435 X0 X1
       grind)
    | exact resolve eq435 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq478 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq425 X1 (σ X0)
       grind)
    | exact superpose eq425 eq24
    | (have j1 := eq425 X1 (σ X0)
       grind)
    | exact resolve eq24 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq489 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq425 (τ X1) X0
       grind)
    | exact superpose eq425 eq17
    | (have j1 := eq425 (τ X1) X0
       grind)
    | exact resolve eq17 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq425
  have eq500 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq478
    | (have j0 := eq478 X0 X1
       grind)
    | exact resolve eq478 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq1925 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq489 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq489
    | exact resolve eq489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq1982 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1925 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1925
    | (have j0 := eq1925 X0 X1
       grind)
    | exact resolve eq1925 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq6744 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq454 x y
       grind)
    | exact superpose eq454 eq16
    | (have j1 := eq454 x y
       grind)
    | exact resolve eq16 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6779 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq454 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq6816 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq6744
       have i₂ := eq1982 y x
       grind)
    | exact superpose eq1982 eq6744
    | (have j1 := eq1982 y x
       grind)
    | (have r₁ := eq6744
       have r₂ := eq1982 y x
       grind)
    | exact resolve eq6744 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6744
  have eq6817 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6816
  have eq6821 : y ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6817
       grind)
    | exact superpose eq6817 eq12
    | exact resolve eq12 eq6817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6822 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6817
       grind)
    | exact superpose eq6817 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6817
       grind)
    | exact resolve eq13 eq6817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6817
  have eq6829 : (k y x) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6822
  have eq6830 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6821
       have r₂ := eq6829
       grind)
    | exact resolve eq6821 eq6829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6821 eq6829
  have eq6966 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq346 x y
       have i₂ := eq6830
       grind)
    | exact superpose eq6830 eq346
    | (have j0 := eq346 x y
       grind)
    | exact resolve eq346 eq6830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq6976 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6966
  have eq6977 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6976
  have eq6989 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq500 x (σ y)
       have i₂ := eq6977
       grind)
    | exact superpose eq6977 eq500
    | (have j0 := eq500 x (σ y)
       grind)
    | exact resolve eq500 eq6977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq6993 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq6977
       grind)
    | exact superpose eq6977 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6977
       grind)
    | exact resolve eq12 eq6977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7000 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6977
  have eq7001 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6993
  have eq7002 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq7001
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq7001
    | exact resolve eq7001 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7001
  have eq7004 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6989
       have r₂ := eq7000
       grind)
    | exact resolve eq6989 eq7000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989
  have eq7009 : y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7004
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq7004
    | exact resolve eq7004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7181 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6830
       have i₂ := eq7009
       grind)
    | exact superpose eq7009 eq6830
    | exact resolve eq6830 eq7009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7009
  have eq7202 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq7181
  have eq7214 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq7202
       grind)
    | exact superpose eq7202 eq12
    | exact resolve eq12 eq7202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7215 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq7202
       grind)
    | exact superpose eq7202 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq7202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7202
  have eq7222 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq7215
       have r₂ := eq67 x
       grind)
    | exact resolve eq7215 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7215
  have eq7223 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7214
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq7214
    | exact resolve eq7214 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214
  have eq7224 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7222
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq7222
    | exact resolve eq7222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7222
  have eq7225 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7224
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq7224
    | exact resolve eq7224 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7224
  have eq7226 : y = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7225
       have r₂ := eq7223
       grind)
    | exact resolve eq7225 eq7223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7223 eq7225
  have eq7431 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7000
       have i₂ := eq7226
       grind)
    | exact superpose eq7226 eq7000
    | exact resolve eq7000 eq7226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7000 eq7226
  have eq7432 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq7431
  have eq7555 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq7002
       grind)
    | exact superpose eq7002 eq12
    | exact resolve eq12 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7556 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq7002
       grind)
    | exact superpose eq7002 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7002
  have eq7563 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq7556
       have r₂ := eq67 x
       grind)
    | exact resolve eq7556 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7556
  have eq7564 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq7555
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq7555
    | exact resolve eq7555 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7555
  have eq7565 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq7563
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq7563
    | exact resolve eq7563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7563
  have eq7566 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq7565
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq7565
    | exact resolve eq7565 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq7565
  have eq7567 : (σ y) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7566
       have r₂ := eq7564
       grind)
    | exact resolve eq7566 eq7564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7564 eq7566
  have eq7729 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq7567
  have eq8688 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6779 x y
       have i₂ := eq6830
       grind)
    | exact superpose eq6830 eq6779
    | (have j0 := eq6779 x y
       grind)
    | exact resolve eq6779 eq6830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6779 eq6830
  have eq8716 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq8688
  have eq8717 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq8716
  have eq8853 : (σ y) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7432
       have i₂ := eq8717
       grind)
    | exact superpose eq8717 eq7432
    | exact resolve eq7432 eq8717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7432
  have eq8854 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8717
       grind)
    | exact superpose eq8717 eq16
    | exact resolve eq16 eq8717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8717
  have eq8870 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq8853
       have r₂ := eq7729
       grind)
    | exact resolve eq8853 eq7729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7729 eq8853
  have eq8993 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1982 y x
       have i₂ := eq8870
       grind)
    | exact superpose eq8870 eq1982
    | (have j0 := eq1982 y x
       grind)
    | exact resolve eq1982 eq8870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982 eq8870
  have eq9074 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq8993
       have r₂ := eq8854
       grind)
    | exact resolve eq8993 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8993
  have eq9210 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8854
       have i₂ := eq9074
       grind)
    | exact superpose eq9074 eq8854
    | exact resolve eq8854 eq9074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8854 eq9074
  have eq9221 : False := by grind
  exact eq9221

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation2533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq328 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq353 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq328 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq328
    | (have j0 := eq328 X0 X1
       grind)
    | exact resolve eq328 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq328
  have eq358 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq353 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq353 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq353 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq361 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq358 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq358
    | (have j0 := eq358 X0 X1
       grind)
    | exact resolve eq358 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq358
  have eq459 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq361
    | exact resolve eq361 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq361 (σ X0) X1
       grind)
    | exact superpose eq361 eq15
    | (have j1 := eq361 (σ X0) X1
       grind)
    | exact resolve eq15 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq489 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq466
    | (have j0 := eq466 X0 X1
       grind)
    | exact resolve eq466 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq517 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq459 (τ X1) X0
       grind)
    | exact superpose eq459 eq17
    | (have j1 := eq459 (τ X1) X0
       grind)
    | exact resolve eq17 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq459
  have eq801 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq517
    | exact resolve eq517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq847 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq801 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq801
    | (have j0 := eq801 X0 X1
       grind)
    | exact resolve eq801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq3246 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq489 x y
       grind)
    | exact superpose eq489 eq16
    | (have j1 := eq489 x y
       grind)
    | exact resolve eq16 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3273 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq489 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq3524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3246
       have i₂ := eq847 y x
       grind)
    | exact superpose eq847 eq3246
    | (have j1 := eq847 y x
       grind)
    | (have r₁ := eq3246
       have r₂ := eq847 y x
       grind)
    | exact resolve eq3246 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246
  have eq3525 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3524
  have eq3529 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3525
       grind)
    | exact superpose eq3525 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq3525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3530 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3525
       grind)
    | exact superpose eq3525 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3525
       grind)
    | exact resolve eq13 eq3525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525
  have eq3535 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3530
  have eq3536 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq3529
       have r₂ := eq3535
       grind)
    | exact resolve eq3529 eq3535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3529 eq3535
  have eq3650 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq345 x y
       have i₂ := eq3536
       grind)
    | exact superpose eq3536 eq345
    | (have j0 := eq345 x y
       grind)
    | exact resolve eq345 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq3660 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3650
  have eq3661 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3660
  have eq3675 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3661
       grind)
    | exact superpose eq3661 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3661
       grind)
    | exact resolve eq12 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq3681 : (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3675
  have eq3686 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq3681
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3681
    | exact resolve eq3681 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3681
  have eq3948 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq3686
       grind)
    | exact superpose eq3686 eq12
    | exact resolve eq12 eq3686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3949 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3686
       grind)
    | exact superpose eq3686 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq3686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3686
  have eq3956 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq3949
       have r₂ := eq66 x
       grind)
    | exact resolve eq3949 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3949
  have eq3957 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq3948
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3948
    | exact resolve eq3948 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948
  have eq3958 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq3956
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3956
    | exact resolve eq3956 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq3959 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq3958
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq3958
    | exact resolve eq3958 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3958
  have eq3960 : (σ x) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq3959
       have r₂ := eq3957
       grind)
    | exact resolve eq3959 eq3957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3957 eq3959
  have eq4043 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq3960
  have eq4211 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3273 x y
       have i₂ := eq3536
       grind)
    | exact superpose eq3536 eq3273
    | (have j0 := eq3273 x y
       grind)
    | exact resolve eq3273 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273 eq3536
  have eq4239 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4211
  have eq4240 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4239
  have eq4409 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4240
       grind)
    | exact superpose eq4240 eq16
    | exact resolve eq16 eq4240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4413 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4240
       grind)
    | exact superpose eq4240 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq4240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4240
  have eq4420 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4413
       have r₂ := eq66 x
       grind)
    | exact resolve eq4413 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4413
  have eq4422 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4420
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4420
    | exact resolve eq4420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4420
  have eq4423 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4422
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq4422
    | exact resolve eq4422 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq4422
  have eq4424 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4423
       have r₂ := eq4043
       grind)
    | exact resolve eq4423 eq4043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4043 eq4423
  have eq4544 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq847 y x
       have i₂ := eq4424
       grind)
    | exact superpose eq4424 eq847
    | (have j0 := eq847 y x
       grind)
    | exact resolve eq847 eq4424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq4424
  have eq4603 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq4544
       have r₂ := eq4409
       grind)
    | exact resolve eq4544 eq4409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4544
  have eq4680 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4409
       have i₂ := eq4603
       grind)
    | exact superpose eq4603 eq4409
    | exact resolve eq4409 eq4603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4409 eq4603
  have eq4694 : False := by grind
  exact eq4694
