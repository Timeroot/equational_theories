import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxy_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq125 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k (M.op x y) (k y x))) = (k (σ (M.op x y)) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq37 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq37
    | exact resolve eq37 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq150 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq211 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq316 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq293
    | exact resolve eq293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq293 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq293
    | (have j0 := eq293 X0 x
       grind)
    | exact resolve eq293 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq618 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X1) X1 X2 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq687 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq686 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq686
    | exact resolve eq686 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq688 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq685
    | exact resolve eq685 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq689 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq684
    | exact resolve eq684 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq757 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op (M.op X0 X1) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq758 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq757 X0 X1
       have i₂ := eq679 X1 (M.op X0 X1)
       grind)
    | exact superpose eq679 eq757
    | exact resolve eq757 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq761 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq761
    | exact resolve eq761 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq765 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq762
       have r₂ := eq27
       grind)
    | exact resolve eq762 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq767 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq765
    | exact resolve eq765 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq769 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq767
    | exact resolve eq767 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq771 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq769 eq27
    | exact resolve eq27 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq769 eq76
    | (have r₁ := eq76
       have r₂ := eq769
       grind)
    | exact resolve eq76 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq780 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq769
  have eq781 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq774
  have eq833 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq862 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq781
       have r₂ := eq780
       grind)
    | exact resolve eq781 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq781
  have eq865 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq862 eq114
    | exact resolve eq114 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq862 eq82
    | exact resolve eq82 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq869 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq865
  have eq873 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq866
    | exact resolve eq866 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq874 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq869
       have r₂ := eq771
       grind)
    | exact resolve eq869 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq869
  have eq877 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq873
       have r₂ := eq75
       grind)
    | exact resolve eq873 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq917 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq874 eq51
    | exact resolve eq51 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq874 eq64
    | (have r₁ := eq64
       have r₂ := eq874
       grind)
    | exact resolve eq64 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq874 eq221
    | exact resolve eq221 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq918
  have eq1004 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq877
       grind)
    | exact superpose eq877 eq72
    | exact resolve eq72 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq1009 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1004
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1004
    | exact resolve eq1004 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1015 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1009 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1016 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1015
  have eq1020 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1016
    | exact resolve eq1016 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1023 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1020
    | exact resolve eq1020 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1024 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1023
  have eq1027 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1024 eq27
    | exact resolve eq27 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1083 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq224 eq51
    | exact resolve eq51 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq224
  have eq1104 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq221 eq1083
    | exact resolve eq1083 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1147 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq925 eq114
    | exact resolve eq114 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1148 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq925 eq82
    | exact resolve eq82 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1150 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1147
  have eq1163 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1150 eq920
    | exact resolve eq920 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1170 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1163
  have eq1228 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1170 eq14
    | exact resolve eq14 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1316 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X3)) (M.op X3 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq646 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq646
    | exact resolve eq646 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1353 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq646 X0 X0 X0
       grind)
    | exact superpose eq646 eq14
    | exact resolve eq14 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1354 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq646 X0 X0 X0
       grind)
    | exact superpose eq646 eq50
    | exact resolve eq50 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1366 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq679 (M.op x (M.op x x)) x
       have i₂ := eq646 x x x
       grind)
    | exact superpose eq646 eq679
    | exact resolve eq679 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1511 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1150 eq1148
    | exact resolve eq1148 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1528 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1511
  have eq1530 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq1528
    | exact resolve eq1528 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq1583 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq917 (M.op X0 (M.op X0 X0))
       have i₂ := eq646 X0 X0 X0
       grind)
    | exact superpose eq646 eq917
    | exact resolve eq917 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1802 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq221 eq758
    | exact resolve eq758 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq221 eq758
    | exact resolve eq758 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1823 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1802
       have i₂ := eq53 sF3 sF4
       grind)
    | exact superpose eq53 eq1802
    | exact resolve eq1802 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq1956 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1228 (M.op sF1 sF1) x
       have i₂ := eq679 sF1 x
       grind)
    | exact superpose eq679 eq1228
    | exact resolve eq1228 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1994 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1956
       have i₂ := eq53 sF1 sF1
       grind)
    | exact superpose eq53 eq1956
    | exact resolve eq1956 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq2008 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1994 eq622
    | exact resolve eq622 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq1994
  have eq3112 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq874 eq2008
    | exact resolve eq2008 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3126 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq3112
  have eq3520 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq624 X0 X0 (M.op X0 X0) x
       have i₂ := eq646 x X0 X0
       grind)
    | exact superpose eq646 eq624
    | exact resolve eq624 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq3536 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq623 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       have i₂ := eq624 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq624 eq623
    | exact resolve eq623 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq4109 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1
       have i₂ := eq688 X0 X1
       grind)
    | exact superpose eq688 eq689
    | exact resolve eq689 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq4167 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq4109
    | (have j0 := eq4109 (σ x) (σ y)
       grind)
    | exact resolve eq4109 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109
  have eq4232 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq221 eq4167
    | exact resolve eq4167 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4167
  have eq4856 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq687 X0 X1 X2 X3
       have i₂ := eq688 X0 X1
       grind)
    | exact superpose eq688 eq687
    | exact resolve eq687 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq5079 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))))) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq674 (M.op X0 (M.op X1 X2)) X1 X2
       have i₂ := eq4856 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)) (M.op X1 X2) X0
       grind)
    | exact superpose eq4856 eq674
    | exact resolve eq674 eq4856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq4856
  have eq5099 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op y (M.op (M.op x y) (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))))) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5079 X0 X1 X2
       have i₂ := eq53 X0 (M.op X1 X2)
       grind)
    | exact superpose eq53 eq5079
    | exact resolve eq5079 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq5079
  have eq5122 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op y (M.op (M.op x y) (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))))) (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5099 X0 X1 X2
       have i₂ := eq688 X0 (M.op X1 X2)
       grind)
    | exact superpose eq688 eq5099
    | exact resolve eq5099 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq5099
  have eq5126 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X2)) (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq623 eq5122
    | exact resolve eq5122 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5122
  have eq5476 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq95 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95
    | (have j0 := eq95 y
       grind)
    | exact resolve eq95 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq5503 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5476
  have eq5509 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5503
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq5503
    | exact resolve eq5503 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq5503
  have eq5519 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5509
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5509 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509
  have eq5552 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq135
    | (have j0 := eq135 (M.op x y)
       grind)
    | exact resolve eq135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq5579 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5552
  have eq5584 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq5579
    | exact resolve eq5579 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5579
  have eq5595 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5584
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5584 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5584
  have eq5711 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1170 eq3126
    | exact resolve eq3126 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq3126
  have eq5745 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5711
  have eq5994 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq618 X0
       have i₂ := eq1583 X0
       grind)
    | exact superpose eq1583 eq618
    | exact resolve eq618 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq6164 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5994
    | (have j0 := eq5994 (σ y)
       grind)
    | exact resolve eq5994 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6181 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5994 eq669
    | exact resolve eq669 eq5994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq5994
  have eq6232 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6181 x x
       have i₂ := eq679 sF3 (M.op x x)
       grind)
    | exact superpose eq679 eq6181
    | exact resolve eq6181 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6181
  have eq6234 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq6232
    | exact resolve eq6232 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6232
  have eq6352 : (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6234 eq758
    | exact resolve eq758 eq6234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq6367 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq221 eq6352
    | exact resolve eq6352 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6352
  have eq6373 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq874 eq6164
    | exact resolve eq6164 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6393 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6164 eq1228
    | exact resolve eq1228 eq6164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228 eq6164
  have eq6399 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6393
  have eq6403 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6373
  have eq6826 : (σ x) = (k (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq874 eq6367
    | exact resolve eq6367 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6831 : (σ x) = (k (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6826
  have eq6833 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1150 eq6403
    | exact resolve eq6403 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403
  have eq6862 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6833
  have eq6870 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6862 eq5745
    | exact resolve eq5745 eq6862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5745
  have eq6899 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6870
  have eq6939 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6899 eq917
    | exact resolve eq917 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq6970 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6939
  have eq6985 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq6970
    | exact resolve eq6970 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6970
  have eq7156 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6985 eq6367
    | exact resolve eq6367 eq6985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6367
  have eq7185 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7156
  have eq7261 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7185 eq150
    | exact resolve eq150 eq7185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7185
  have eq7659 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1150 eq6831
    | exact resolve eq6831 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq6831
  have eq7664 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7659
  have eq7668 : (τ (σ x)) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7664 eq150
    | exact resolve eq150 eq7664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq7664
  have eq7672 : x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq7668
    | exact resolve eq7668 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7668
  have eq7675 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7672 eq7261
    | exact resolve eq7261 eq7672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7261
  have eq7678 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7675
  have eq7708 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7678 eq428
    | exact resolve eq428 eq7678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq7678
  have eq7717 : ∀ X0 : G, (τ (k X0 (σ x))) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7708 X0
       have i₂ := eq443 X0
       grind)
    | exact superpose eq443 eq7708
    | exact resolve eq7708 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq7708
  have eq9159 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq833 x y
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq833
    | (have j0 := eq833 x y
       grind)
    | exact resolve eq833 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq9182 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9159
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9159
    | exact resolve eq9159 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9159
  have eq9220 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9182
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9182
    | exact resolve eq9182 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9182
  have eq9256 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9220
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9220
    | exact resolve eq9220 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9220
  have eq9288 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9256
    | exact resolve eq9256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9256
  have eq9318 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9288
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9288
    | exact resolve eq9288 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9288
  have eq9342 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9318
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9318
    | exact resolve eq9318 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9318
  have eq9352 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9342
    | exact resolve eq9342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9342
  have eq19085 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6862 eq6399
    | exact resolve eq6399 eq6862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6399 eq6862
  have eq19136 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19085
  have eq23188 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op y (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6234 eq1354
    | exact resolve eq1354 eq6234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6234
  have eq26050 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1104 eq1823
    | exact resolve eq1823 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq1823
  have eq29678 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4232 eq26050
    | exact resolve eq26050 eq4232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26050
  have eq32519 : (k (σ (M.op x y)) (k (σ y) (σ x))) = (σ (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq129
       have i₂ := eq1530
       grind)
    | exact superpose eq1530 eq129
    | exact resolve eq129 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1530
  have eq32574 : (k (σ (M.op x y)) (k (σ y) (σ x))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq32519
    | exact resolve eq32519 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq32519
  have eq32582 : (k (σ (M.op x y)) (k (σ y) (σ x))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5595 eq32574
    | exact resolve eq32574 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32574
  have eq34024 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq925 eq32582
    | exact resolve eq32582 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq32582
  have eq34046 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq34024
  have eq42456 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5519 eq109
    | exact resolve eq109 eq5519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq5519
  have eq52935 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19136 eq1353
    | exact resolve eq1353 eq19136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353 eq19136
  have eq53199 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op y (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52935
       have i₂ := eq1354 sF3
       grind)
    | exact superpose eq1354 eq52935
    | exact resolve eq52935 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354 eq52935
  have eq53759 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53199 eq23188
    | exact resolve eq23188 eq53199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23188 eq53199
  have eq53821 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq53759
  have eq54123 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6985 eq1812
    | exact resolve eq1812 eq6985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812 eq6985
  have eq54164 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53821 eq2008
    | exact resolve eq2008 eq53821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008 eq53821
  have eq54248 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq54164
  have eq54263 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4232 eq54248
    | exact resolve eq54248 eq4232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232 eq54248
  have eq61423 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54263 eq29678
    | exact resolve eq29678 eq54263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29678 eq54263
  have eq75590 : (M.op (σ y) (σ x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq874 eq61423
    | exact resolve eq61423 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq61423
  have eq75605 : (M.op (σ y) (σ x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq75590
  have eq273595 : (τ (σ (M.op x y))) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54123 eq7717
    | exact resolve eq7717 eq54123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7717 eq54123
  have eq273845 : (τ (σ (M.op x y))) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq273595
  have eq274070 : (M.op x y) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq273845
    | exact resolve eq273845 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq273845
  have eq274083 : (M.op x y) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75605 eq274070
    | exact resolve eq274070 eq75605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75605 eq274070
  have eq274299 : (M.op x y) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq274083
  have eq274332 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (M.op (σ y) (σ x)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq274299 eq316
    | exact resolve eq316 eq274299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq274299
  have eq337333 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op (σ x) X0) (M.op X0 (M.op X0 X0)))) (M.op (M.op (σ x) X0) (M.op X0 (M.op X0 X0)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1583 eq3536
    | exact resolve eq3536 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq3536
  have eq337897 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq337333 X0 X1
       have i₂ := eq1366 X0 sF2
       grind)
    | exact superpose eq1366 eq337333
    | exact resolve eq337333 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337333
  have eq338086 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq623 eq337897
    | exact resolve eq337897 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq337897
  have eq339118 : (M.op y y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq338086 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq338086
    | (have j0 := eq338086 y x
       grind)
    | exact resolve eq338086 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519520 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34046 eq274332
    | exact resolve eq274332 eq34046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34046 eq274332
  have eq519744 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq519520
  have eq519757 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6899 eq519744
    | exact resolve eq519744 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6899 eq519744
  have eq519984 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq519757
  have eq520145 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq519984
    | exact resolve eq519984 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq519984
  have eq520283 : y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq520145 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq520145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520145
  have eq520297 : y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq520283
  have eq520307 : y = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq211 eq520297
    | exact resolve eq520297 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520297
  have eq520356 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq211 eq520307
    | exact resolve eq520307 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520307
  have eq554138 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq520356 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | (have r₁ := eq12 (M.op x y) y
       have r₂ := eq520356
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq520356
       grind)
    | exact resolve eq12 eq520356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520356
  have eq554321 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq554138
  have eq554322 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq554321
  have eq558531 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq554322 eq7672
    | exact resolve eq7672 eq554322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554322
  have eq558551 : y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq558531
  have eq558671 : y ≠ y ∨ (M.op (M.op x y) y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq558551 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq558551
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq558551
       grind)
    | exact resolve eq13 eq558551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558551
  have eq558856 : (M.op (M.op x y) y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq558671
  have eq561863 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq558856 eq7672
    | exact resolve eq7672 eq558856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7672 eq558856
  have eq561881 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq561863
  have eq561937 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq561881 eq339118
    | exact resolve eq339118 eq561881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339118 eq561881
  have eq562137 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq561937
  have eq563757 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq338086 y y
       have i₂ := eq562137
       grind)
    | exact superpose eq562137 eq338086
    | exact resolve eq338086 eq562137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338086 eq562137
  have eq563769 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq563757
  have eq563791 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq563769
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq563769
    | exact resolve eq563769 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563769
  have eq563792 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq563791
  have eq564799 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq563792 eq20
    | exact resolve eq20 eq563792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564806 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq563792 eq75
    | (have r₁ := eq75
       have r₂ := eq563792
       grind)
    | exact resolve eq75 eq563792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq564811 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq563792 eq125
    | exact resolve eq125 eq563792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq565076 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq563792
  have eq565079 : x = y ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq564806
  have eq565206 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq564811 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq564811
    | exact resolve eq564811 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq564811
  have eq565214 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq564799
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq564799
    | exact resolve eq564799 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564799
  have eq566032 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq565214 eq1027
    | (have r₁ := eq1027
       have r₂ := eq565214
       grind)
    | exact resolve eq1027 eq565214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq567514 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq566032
  have eq567515 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq567514
  have eq567597 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq567515 eq27
    | exact resolve eq27 eq567515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567599 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq567515 eq64
    | (have r₁ := eq64
       have r₂ := eq567515
       grind)
    | exact resolve eq64 eq567515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq567601 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq567515 eq221
    | exact resolve eq221 eq567515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq569026 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq567599
  have eq584481 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq569026 eq565206
    | exact resolve eq565206 eq569026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565206
  have eq584494 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq584481
  have eq594520 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq565079
       have r₂ := eq565076
       grind)
    | exact resolve eq565079 eq565076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565076 eq565079
  have eq594524 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq594520
       grind)
    | exact superpose eq594520 eq72
    | exact resolve eq72 eq594520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594520
  have eq594597 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq594524
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq594524
    | exact resolve eq594524 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594524
  have eq594662 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq565214 eq594597
    | exact resolve eq594597 eq565214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565214
  have eq594700 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq594597 eq569026
    | exact resolve eq569026 eq594597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569026 eq594597
  have eq594717 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq594700
  have eq594749 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq594662
  have eq594815 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq594749 eq584494
    | exact resolve eq584494 eq594749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584494 eq594749
  have eq594832 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq594815
  have eq594964 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq594717 eq567601
    | exact resolve eq567601 eq594717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567601 eq594717
  have eq595190 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq594964
  have eq597561 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq595190 eq1366
    | exact resolve eq1366 eq595190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366 eq595190
  have eq597903 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq597561
    | exact resolve eq597561 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597561
  have eq599808 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq567515 eq597903
    | exact resolve eq597903 eq567515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567515 eq597903
  have eq600291 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq599808
  have eq604613 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq600291 eq594832
    | exact resolve eq594832 eq600291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594832 eq600291
  have eq604837 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq604613
  have eq604981 : x = (M.op x y) := by
    first
    | (have r₁ := eq604837
       have r₂ := eq567597
       grind)
    | exact resolve eq604837 eq567597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567597 eq604837
  have eq605774 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq604981 eq20
    | exact resolve eq20 eq604981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq605776 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq604981 eq50
    | exact resolve eq50 eq604981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq605778 : x ≠ x ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq604981 eq63
    | (have r₁ := eq63
       have r₂ := eq604981
       grind)
    | exact resolve eq63 eq604981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq605815 : (M.op y x) = (M.op x x) := by
    first
    | exact superpose eq604981 eq211
    | exact resolve eq211 eq604981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq606055 : (k y x) = (M.op y x) := by grind
  clear eq605778
  have eq606204 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq605774
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq605774
    | exact resolve eq605774 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605774
  have eq606224 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq606204 eq26
    | exact resolve eq26 eq606204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq606363 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq606204 eq9352
    | exact resolve eq9352 eq606204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9352
  have eq607142 : (σ y) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq606363
       have r₂ := eq27
       grind)
    | exact resolve eq606363 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606363
  have eq607761 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq606055
       have i₂ := eq605815
       grind)
    | exact superpose eq605815 eq606055
    | exact resolve eq606055 eq605815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605815 eq606055
  have eq609789 : (k (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq607761
       grind)
    | exact superpose eq607761 eq72
    | exact resolve eq72 eq607761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq607761
  have eq609854 : (k (σ y) (σ (M.op x y))) = (σ (M.op x x)) := by
    first
    | exact superpose eq606204 eq609789
    | exact resolve eq609789 eq606204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609789
  have eq614364 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq5126 y x (M.op X0 X0)
       have i₂ := eq605776 X0
       grind)
    | exact superpose eq605776 eq5126
    | exact resolve eq5126 eq605776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5126 eq605776
  have eq614683 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | exact superpose eq604981 eq614364
    | exact resolve eq614364 eq604981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614364
  have eq620376 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op y y)) y) := by
    intro X0
    first
    | (have i₁ := eq1316 y x X0 y
       have i₂ := eq614683 y
       grind)
    | exact superpose eq614683 eq1316
    | exact resolve eq1316 eq614683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq614683
  have eq620884 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq620376 x
       have i₂ := eq679 y x
       grind)
    | exact superpose eq679 eq620376
    | exact resolve eq620376 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq620376
  have eq621000 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq620884
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq620884
    | exact resolve eq620884 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq620884
  have eq621045 : x = (M.op y y) := by
    first
    | exact superpose eq604981 eq621000
    | exact resolve eq621000 eq604981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604981 eq621000
  have eq621080 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq42456
       have i₂ := eq621045
       grind)
    | exact superpose eq621045 eq42456
    | exact resolve eq42456 eq621045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42456
  have eq621631 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq621080
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq621080
    | exact resolve eq621080 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621080
  have eq621720 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq606204 eq621631
    | exact resolve eq621631 eq606204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621631
  have eq630235 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq621720 eq3520
    | exact resolve eq3520 eq621720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520 eq621720
  have eq630646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq606224 eq630235
    | exact resolve eq630235 eq606224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606224 eq630235
  have eq630728 : x = y := by
    first
    | (have r₁ := eq630646
       have r₂ := eq27
       grind)
    | exact resolve eq630646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630646
  have eq630803 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq630728
       grind)
    | exact superpose eq630728 eq24
    | exact resolve eq24 eq630728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq631195 : x = (M.op x x) := by
    first
    | (have i₁ := eq621045
       have i₂ := eq630728
       grind)
    | exact superpose eq630728 eq621045
    | exact resolve eq621045 eq630728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621045 eq630728
  have eq631564 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq630803
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq630803
    | exact resolve eq630803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630803
  have eq631725 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq606204 eq631564
    | exact resolve eq631564 eq606204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631564
  have eq632680 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq631725 eq607142
    | exact resolve eq607142 eq631725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607142
  have eq632697 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq632680
       have r₂ := eq27
       grind)
    | exact resolve eq632680 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq632680
  have eq632773 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5595 eq632697
    | exact resolve eq632697 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632697
  have eq632876 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq609854
       have i₂ := eq631195
       grind)
    | exact superpose eq631195 eq609854
    | exact resolve eq609854 eq631195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609854 eq631195
  have eq633399 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq631725 eq632876
    | exact resolve eq632876 eq631725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631725 eq632876
  have eq633519 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5595 eq633399
    | exact resolve eq633399 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595 eq633399
  have eq633584 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq633519
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq633519
    | exact resolve eq633519 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq633519
  have eq633621 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq606204 eq633584
    | exact resolve eq633584 eq606204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606204 eq633584
  have eq638896 : False := by grind
  exact eq638896

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyy_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq89 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq82
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq100
  have eq168 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  have eq190 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq462 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq615 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X1 X0) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq779 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq462 eq14
    | exact resolve eq14 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq788 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq779 X0
       have i₂ := eq54 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq54 eq779
    | exact resolve eq779 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq791 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq788 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq788
    | exact resolve eq788 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq1392 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq527 X0 X0 X0
       grind)
    | exact superpose eq527 eq14
    | exact resolve eq14 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1394 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq527 X0 X0 X0
       grind)
    | exact superpose eq527 eq51
    | exact resolve eq51 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1667 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq471 X0
       have i₂ := eq1394 X0
       grind)
    | exact superpose eq1394 eq471
    | exact resolve eq471 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq1739 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq51 eq1667
    | exact resolve eq1667 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1667
  have eq1862 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq615 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq471 X0
       grind)
    | exact superpose eq471 eq615
    | exact resolve eq615 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq615
  have eq1958 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1862 X0
       have i₂ := eq54 X0 (M.op X0 X0)
       grind)
    | exact superpose eq54 eq1862
    | exact resolve eq1862 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq1974 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1958 X0
       have i₂ := eq791 X0
       grind)
    | exact superpose eq791 eq1958
    | exact resolve eq1958 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq1958
  have eq2573 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq1974 (M.op x (M.op x x))
       have i₂ := eq527 x x x
       grind)
    | exact superpose eq527 eq1974
    | exact resolve eq1974 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq1974
  have eq2594 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2573 X0
       have i₂ := eq558 X0 X0
       grind)
    | exact superpose eq558 eq2573
    | exact resolve eq2573 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq2573
  have eq6112 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq168 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq168
    | (have j0 := eq168 x
       grind)
    | exact resolve eq168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq6136 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6112
  have eq6144 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6136
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6136
    | exact resolve eq6136 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6136
  have eq6151 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6144
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6144 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6144
  have eq6157 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6151 eq50
    | exact resolve eq50 eq6151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq6226 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq190 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq190
    | (have j0 := eq190 y
       grind)
    | exact resolve eq190 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq6249 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6226
  have eq6256 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6249
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq6249
    | exact resolve eq6249 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6249
  have eq6265 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6256
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6256 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6256
  have eq6273 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6265 eq105
    | exact resolve eq105 eq6265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq16061 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6151 eq89
    | exact resolve eq89 eq6151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq16432 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6265 eq106
    | exact resolve eq106 eq6265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq22594 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq548 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1392 X0 X0 X1
       grind)
    | exact superpose eq1392 eq548
    | exact resolve eq548 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq22678 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22594 X0 X1 x x x
       have i₂ := eq548 X0 X0 x x x
       grind)
    | exact superpose eq548 eq22594
    | exact resolve eq22594 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq22594
  have eq25068 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq16061
       grind)
    | exact superpose eq16061 eq16
    | exact resolve eq16 eq16061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16061
  have eq25126 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6157 eq25068
    | exact resolve eq25068 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6157 eq25068
  have eq25138 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq25126
       have r₂ := eq13 x x
       grind)
    | exact resolve eq25126 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25126
  have eq25140 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq25138
       grind)
    | exact superpose eq25138 eq44
    | exact resolve eq44 eq25138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq25138
  have eq25172 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq6151 eq25140
    | exact resolve eq25140 eq6151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6151 eq25140
  have eq25526 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq16432
       grind)
    | exact superpose eq16432 eq16
    | exact resolve eq16 eq16432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16432
  have eq25588 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6273 eq25526
    | exact resolve eq25526 eq6273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25526
  have eq25600 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq25588
       have r₂ := eq13 y y
       grind)
    | exact resolve eq25588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25588
  have eq25602 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq25600
       grind)
    | exact superpose eq25600 eq74
    | exact resolve eq74 eq25600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq25634 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq6265 eq25602
    | exact resolve eq25602 eq6265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6265 eq25602
  have eq32196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq32196
    | exact resolve eq32196 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32196
  have eq32208 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq32197
       have r₂ := eq28
       grind)
    | exact resolve eq32197 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32197
  have eq32253 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32208 eq22678
    | exact resolve eq22678 eq32208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33232 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32253 eq32208
    | exact resolve eq32208 eq32253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32208 eq32253
  have eq33275 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq33232
  have eq33330 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq33275 eq2594
    | exact resolve eq2594 eq33275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594 eq33275
  have eq33391 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq33330
    | exact resolve eq33330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33330
  have eq33536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq33391 eq92
    | exact resolve eq92 eq33391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq33391
  have eq33548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq33536
  have eq33551 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq33548
       have r₂ := eq28
       grind)
    | exact resolve eq33548 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33548
  have eq33557 : (τ (σ x)) = (k y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33551 eq6273
    | exact resolve eq6273 eq33551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6273 eq33551
  have eq33681 : (τ (σ x)) = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33557
       have i₂ := eq25600
       grind)
    | exact superpose eq25600 eq33557
    | exact resolve eq33557 eq25600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25600 eq33557
  have eq33693 : x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq33681
    | exact resolve eq33681 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq33681
  have eq33694 : y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq33693
  have eq33700 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq33694
       grind)
    | exact superpose eq33694 eq54
    | exact resolve eq54 eq33694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33738 : (M.op x x) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22678 x y
       have i₂ := eq33694
       grind)
    | exact superpose eq33694 eq22678
    | exact resolve eq22678 eq33694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33754 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33700
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33700
    | exact resolve eq33700 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33700
  have eq33783 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25634
       have i₂ := eq33754
       grind)
    | exact superpose eq33754 eq25634
    | exact resolve eq25634 eq33754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33754
  have eq33908 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq33783
    | exact resolve eq33783 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33783
  have eq34132 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33694
       have i₂ := eq33738
       grind)
    | exact superpose eq33738 eq33694
    | exact resolve eq33694 eq33738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33694 eq33738
  have eq34175 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq34132
  have eq34184 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25172
       have i₂ := eq34175
       grind)
    | exact superpose eq34175 eq25172
    | exact resolve eq25172 eq34175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25172 eq34175
  have eq34318 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq34184
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34184
    | exact resolve eq34184 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq34184
  have eq35210 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq34318 eq54
    | exact resolve eq54 eq34318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq34318
  have eq35261 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq35210
    | exact resolve eq35210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35210
  have eq36291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq35261 eq33908
    | exact resolve eq33908 eq35261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33908 eq35261
  have eq36384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq36291
  have eq36414 : x = (M.op y y) := by
    first
    | (have r₁ := eq36384
       have r₂ := eq28
       grind)
    | exact resolve eq36384 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36384
  have eq36455 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq25634
       have i₂ := eq36414
       grind)
    | exact superpose eq36414 eq25634
    | exact resolve eq25634 eq36414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25634
  have eq36548 : x = (M.op x y) := by
    first
    | (have i₁ := eq22678 y y
       have i₂ := eq36414
       grind)
    | exact superpose eq36414 eq22678
    | exact resolve eq22678 eq36414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22678 eq36414
  have eq36549 : x = (M.op x y) := by
    first
    | (have i₁ := eq36548
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36548
    | exact resolve eq36548 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq36548
  have eq36573 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36455
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36455
    | exact resolve eq36455 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36455
  have eq36589 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq36549 eq21
    | exact resolve eq21 eq36549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq36549
  have eq36818 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq36589
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36589
    | exact resolve eq36589 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq36589
  have eq36846 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq36818 eq27
    | exact resolve eq27 eq36818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37095 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq36818 eq36573
    | exact resolve eq36573 eq36818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36573 eq36818
  have eq37158 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq37095 eq1739
    | exact resolve eq1739 eq37095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739 eq37095
  have eq37631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37158 eq36846
    | exact resolve eq36846 eq37158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36846 eq37158
  have eq37632 : False := by grind
  exact eq37632

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq48 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq21 X0 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq12
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq20 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq20 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq21 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq20 X0 x x X3
       grind)
    | exact superpose eq20 eq21
    | exact resolve eq21 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq20 X1 x x X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq20 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71 X0 X1 X2 X3
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq71
    | exact resolve eq71 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq77 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 X1 X2 X3 X4
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq61
    | exact resolve eq61 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq78 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X0 X1 X2 X3 X4
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq56
    | exact resolve eq56 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq97 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq27
    | (have j0 := eq27 (σ X0) (σ X1)
       grind)
    | exact resolve eq27 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq27
    | (have j0 := eq27 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33
    | exact resolve eq33 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (M.op X0 X1) x
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq68
    | exact resolve eq68 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq70 X0 X0 X0
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq70 X0 X0 X0
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68 (M.op x (M.op x x)) x
       have i₂ := eq70 x x x
       grind)
    | exact superpose eq70 eq68
    | exact resolve eq68 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq212 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq70 X0 X0 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq51 X0 X0 (M.op X0 X0) x
       have i₂ := eq70 X0 x X0
       grind)
    | exact superpose eq70 eq51
    | exact resolve eq51 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq51 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq70 X1 x X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq72 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq72 (M.op X4 (M.op X3 X2)) (M.op X0 X1) X2 X3
       have i₂ := eq72 X0 X1 (M.op X3 X2) X4
       grind)
    | exact superpose eq72 eq72
    | exact resolve eq72 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op (M.op (M.op X5 X4) (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq72 X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0))) X2 X3
       have i₂ := eq51 X0 X1 X2 X3
       grind)
    | exact superpose eq51 eq72
    | exact resolve eq72 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X2 X3)) = (M.op X4 (M.op (M.op X5 X4) (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq51 (M.op X2 X3) X3 X4 X5
       have i₂ := eq72 X2 X3 X0 X1
       grind)
    | exact superpose eq72 eq51
    | exact resolve eq51 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op X1 (M.op (M.op (M.op X5 X4) (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq478 X0 X1 X2 X3 X4 X5
       have i₂ := eq404 (M.op (M.op X5 X4) (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq404 eq478
    | exact resolve eq478 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq525 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) = (M.op X2 (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq473 X0 X1 X2 X3 X4
       have i₂ := eq404 X1 X0 X1
       grind)
    | exact superpose eq404 eq473
    | exact resolve eq473 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq527 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq471 X0 X1 X2 X3
       have i₂ := eq404 (M.op X0 X0) (M.op X3 (M.op X2 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq404 eq471
    | exact resolve eq471 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq529 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 X1
       have i₂ := eq404 (M.op X0 X0) X1 (M.op X0 X0)
       grind)
    | exact superpose eq404 eq469
    | exact resolve eq469 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq545 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq522 X0 X1 X2 X3 x x
       have i₂ := eq181 X1 X0 (M.op x x)
       grind)
    | exact superpose eq181 eq522
    | exact resolve eq522 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq522
  have eq547 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X1 (M.op X1 (M.op X0 X1)))) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq525 X0 X1 X2 X3 X4
       have i₂ := eq404 (M.op X0 X1) (M.op X4 (M.op X3 X2)) (M.op X0 X1)
       grind)
    | exact superpose eq404 eq525
    | exact resolve eq525 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq549 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq527 X0 X1 X2 X3
       have i₂ := eq404 (M.op X3 (M.op X2 X1)) X0 X0
       grind)
    | exact superpose eq404 eq527
    | exact resolve eq527 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq550 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X0 X0) (M.op X0 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1
       have i₂ := eq404 X1 X0 X0
       grind)
    | exact superpose eq404 eq529
    | exact resolve eq529 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq558 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X1 (M.op X1 (M.op X0 X1)))) = (M.op (M.op X0 X1) (M.op X1 (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq547 X0 X1 X2 X3 X4
       have i₂ := eq404 (M.op X4 (M.op X3 X2)) X0 X1
       grind)
    | exact superpose eq404 eq547
    | exact resolve eq547 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq776 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq49 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq70 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq70 eq49
    | exact resolve eq49 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq781 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq776 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq776
    | (have j0 := eq776 X0
       grind)
    | exact resolve eq776 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq794 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq781 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq781
    | (have j0 := eq781 X0
       grind)
    | exact resolve eq781 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq806 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq794
  have eq881 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X0 X1))))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq70 (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X0 X1))) X2 (M.op X0 X1)
       have i₂ := eq77 X0 X1 X3 X4 (M.op X0 X1)
       grind)
    | exact superpose eq77 eq70
    | exact resolve eq70 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq942 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X0 X1))))) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq881 X0 X1 X2 X3 X4
       have i₂ := eq404 X1 X0 X1
       grind)
    | exact superpose eq404 eq881
    | exact resolve eq881 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq1000 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X0 X1))))) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq942 X0 X1 X2 X3 X4
       have i₂ := eq21 (M.op X3 X4) (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq21 eq942
    | exact resolve eq942 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq1035 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X0 X1))))) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1000 X0 X1 X2 X3 X4
       have i₂ := eq404 (M.op X3 X4) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq404 eq1000
    | exact resolve eq1000 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1052 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X3 X4) (M.op X1 (M.op X0 X1))))) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1035 X0 X1 X2 X3 X4
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq1035
    | exact resolve eq1035 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1073 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq806 (σ X0)
       grind)
    | exact superpose eq806 eq15
    | exact resolve eq15 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq125 X0 X0
       have i₂ := eq806 (τ X0)
       grind)
    | exact superpose eq806 eq125
    | exact resolve eq125 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1086 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1075 X0
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq1075
    | exact resolve eq1075 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1088 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1073 X0
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq1073
    | exact resolve eq1073 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq1073
  have eq1960 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ (σ X0)) (σ (σ X1))
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq12
    | (have j0 := eq12 (σ (σ X0)) (σ (σ X1))
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq12 (σ (σ X0)) (σ (σ X1))
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq12 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1984 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X0))) = (k (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1960 X0 X1
       have j1 := eq12 (σ (σ X0)) (σ (σ X1))
       grind)
    | (have r₁ := eq1960 X0 X1
       have r₂ := eq12 (σ (σ X0)) (σ (σ X1))
       grind)
    | exact resolve eq1960 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq2009 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X0))) = (σ (k (σ X0) (σ X1))) ∨ (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1984 X0 X1
       have i₂ := eq15 (σ X0) (σ X1)
       grind)
    | exact superpose eq15 eq1984
    | (have j0 := eq1984 X0 X1
       grind)
    | exact resolve eq1984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984
  have eq2019 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2009 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2009
    | (have j0 := eq2009 X0 X1
       grind)
    | exact resolve eq2009 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009
  have eq2024 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) = (σ (M.op (σ X0) (σ X0))) ∨ (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2019 X0 X1
       have i₂ := eq1088 (σ X0)
       grind)
    | exact superpose eq1088 eq2019
    | (have j0 := eq2019 X0 X1
       grind)
    | exact resolve eq2019 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2029 : ∀ X0 X1 : G, (σ (σ X1)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ (k X0 X1))) = (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2024 X0 X1
       have i₂ := eq1088 X0
       grind)
    | exact superpose eq1088 eq2024
    | (have j0 := eq2024 X0 X1
       grind)
    | exact resolve eq2024 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2057 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq16
    | (have j1 := eq98 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq98 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq98 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq98 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq2081 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2057
  have eq2185 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2081
       grind)
    | exact superpose eq2081 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2081
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2081
       grind)
    | exact resolve eq12 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2199 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2185
  have eq2208 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2199
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2199
    | exact resolve eq2199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq2212 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2208
       have i₂ := eq1088 y
       grind)
    | exact superpose eq1088 eq2208
    | exact resolve eq2208 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208
  have eq2229 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq403 X0
       grind)
    | exact superpose eq403 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq403 X0
       grind)
    | exact resolve eq12 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq2247 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229
  have eq2413 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq212 X0 (σ y) (σ x)
       have i₂ := eq2081
       grind)
    | exact superpose eq2081 eq212
    | exact resolve eq212 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq2468 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X0 (M.op X1 X0) X2 X3
       have i₂ := eq212 X0 X0 X1
       grind)
    | exact superpose eq212 eq51
    | exact resolve eq51 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2487 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X3 (M.op X2 X1)) X0) (M.op X0 (M.op (M.op X3 (M.op X2 X1)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq72 (M.op X3 (M.op X2 X1)) X0 X1 X2
       have i₂ := eq212 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq212 eq72
    | exact resolve eq72 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2491 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X3 (M.op X2 X1)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2487 X0 X1 X2 X3
       have i₂ := eq404 X0 (M.op X3 (M.op X2 X1)) X0
       grind)
    | exact superpose eq404 eq2487
    | exact resolve eq2487 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq2505 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2468 X0 X1 x x
       have i₂ := eq51 X0 X0 x x
       grind)
    | exact superpose eq51 eq2468
    | exact resolve eq2468 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2468
  have eq3344 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq198 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) X2 (M.op X3 X1)
       have i₂ := eq192 X1 X3 X0
       grind)
    | exact superpose eq192 eq198
    | exact resolve eq198 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3346 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)) (M.op (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)) (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)))) = (M.op (M.op X3 (M.op (M.op (M.op X4 X5) (M.op X1 X2)) (M.op (M.op X4 X5) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq198 (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)) X3 (M.op (M.op X4 X5) (M.op X1 X2))
       have i₂ := eq78 X1 X2 X4 X5 X0
       grind)
    | exact superpose eq78 eq198
    | exact resolve eq198 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3358 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq210 X2 X3
       have i₂ := eq198 X2 X0 X1
       grind)
    | exact superpose eq198 eq210
    | exact resolve eq210 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq210
  have eq3510 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)) (M.op (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)) (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)))) = (M.op (M.op X3 (M.op (M.op X1 X2) (M.op (M.op X4 X5) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3346 X0 X1 X2 X3 X4 X5
       have i₂ := eq21 (M.op X4 X5) (M.op X1 X2)
       grind)
    | exact superpose eq21 eq3346
    | exact resolve eq3346 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq3512 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3344 X0 X1 X2 X3
       have i₂ := eq21 X3 X1
       grind)
    | exact superpose eq21 eq3344
    | exact resolve eq3344 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3579 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)) (M.op (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)) (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)))) = (M.op (M.op X3 (M.op X2 (M.op (M.op X4 X5) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3510 X0 X1 X2 X3 X4 X5
       have i₂ := eq404 (M.op X4 X5) X1 X2
       grind)
    | exact superpose eq404 eq3510
    | exact resolve eq3510 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq3581 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3512 X0 X1 X2 X3
       have i₂ := eq404 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)) (M.op X1 (M.op X1 X1)) (M.op X0 X0)
       grind)
    | exact superpose eq404 eq3512
    | exact resolve eq3512 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3512
  have eq3621 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)) (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)))) = (M.op (M.op X3 (M.op X2 (M.op (M.op X4 X5) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3579 X0 X1 X2 X3 X4 X5
       have i₂ := eq404 (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)
       grind)
    | exact superpose eq404 eq3579
    | exact resolve eq3579 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3623 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3581 X0 X1 X2 X3
       have i₂ := eq545 (M.op X1 (M.op X1 X1)) (M.op X0 X0) (M.op X0 X0) (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq545 eq3581
    | exact resolve eq3581 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3581
  have eq3641 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0)))) = (M.op (M.op X3 (M.op X2 (M.op (M.op X4 X5) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3621 X0 X1 X2 X3 X4 X5
       have i₂ := eq545 (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op X0 X0) (M.op X0 X0) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))
       grind)
    | exact superpose eq545 eq3621
    | exact resolve eq3621 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq3621
  have eq3643 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3623 X0 X1 X2 X3
       have i₂ := eq2491 (M.op X0 X0) X1 X1 X1
       grind)
    | exact superpose eq2491 eq3623
    | exact resolve eq3623 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq3652 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op X3 (M.op X2 (M.op (M.op X4 X5) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3641 X0 X1 X2 X3 X4 X5
       have i₂ := eq2491 (M.op X0 X0) (M.op X1 X2) X2 (M.op X1 X2)
       grind)
    | exact superpose eq2491 eq3641
    | exact resolve eq3641 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491 eq3641
  have eq3654 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3643 X0 X1 X2 X3
       have i₂ := eq404 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq404 eq3643
    | exact resolve eq3643 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643
  have eq3657 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X2) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op X3 (M.op X2 (M.op (M.op X4 X5) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3652 X0 X1 X2 X3 X4 X5
       have i₂ := eq404 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq404 eq3652
    | exact resolve eq3652 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652
  have eq3659 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3654 X0 X1 X2 X3
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq3654
    | exact resolve eq3654 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3654
  have eq3661 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 (M.op X2 (M.op (M.op X4 X5) (M.op X1 X2)))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3657 X0 X1 X2 X3 X4 X5
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq3657
    | exact resolve eq3657 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3657
  have eq5183 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2212
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq2212
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op y y))
       grind)
    | exact resolve eq2212 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212
  have eq5211 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq5183
  have eq5334 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X1 (M.op X2 X0)))) = (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 (M.op X1 X2) X2 X1
       have i₂ := eq404 X0 X1 X2
       grind)
    | exact superpose eq404 eq72
    | exact resolve eq72 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5361 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X1 (M.op X2 X0)))) = (M.op X3 (M.op (M.op X4 X3) (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq72 X1 (M.op X2 X0) X3 X4
       have i₂ := eq404 X1 X2 X0
       grind)
    | exact superpose eq404 eq72
    | exact resolve eq72 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq5408 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X1 (M.op X2 X0)))) = (M.op X3 (M.op (M.op X4 X3) (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5361 X0 X1 X2 X3 X4
       have i₂ := eq404 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq404 eq5361
    | exact resolve eq5361 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5361
  have eq5422 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X1 (M.op X2 X0)))) = (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5334 X0 X1 X2
       have i₂ := eq404 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq404 eq5334
    | exact resolve eq5334 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5334
  have eq6011 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 (M.op X1 X0)
       have i₂ := eq212 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq212 eq550
    | exact resolve eq550 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq550
  have eq6159 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6011 X0 X1
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq6011
    | exact resolve eq6011 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6011
  have eq6221 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6159 X0 X1
       have i₂ := eq48 (M.op X0 X0)
       grind)
    | exact superpose eq48 eq6159
    | exact resolve eq6159 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6159
  have eq7129 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X3) (M.op (M.op X1 X1) (M.op X1 X1))) (M.op X0 X1)) = (M.op (M.op X1 (M.op (M.op X4 (M.op X5 X0)) (M.op X1 X1))) (M.op (M.op (M.op X4 (M.op X5 X0)) (M.op X1 X1)) (M.op X1 (M.op (M.op X4 (M.op X5 X0)) (M.op X1 X1))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq77 X1 (M.op (M.op X4 (M.op X5 X0)) (M.op X1 X1)) X2 X3 (M.op X1 X1)
       have i₂ := eq549 X1 X0 X5 X4
       grind)
    | exact superpose eq549 eq77
    | exact resolve eq77 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq7146 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))) (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))) (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq192 (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))) (M.op X1 X1) X4
       have i₂ := eq549 X1 X0 X3 X2
       grind)
    | exact superpose eq549 eq192
    | exact resolve eq192 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq549
  have eq7164 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1)) (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))) (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7146 X0 X1 X2 X3 X4
       have i₂ := eq404 (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))) X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))
       grind)
    | exact superpose eq404 eq7146
    | exact resolve eq7146 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq7146
  have eq7175 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X3) (M.op (M.op X1 X1) (M.op X1 X1))) (M.op X0 X1)) = (M.op (M.op X4 (M.op X5 X0)) (M.op X1 X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq7129 X0 X1 X2 X3 X4 X5
       have i₂ := eq3358 (M.op X4 (M.op X5 X0)) X1 (M.op (M.op X4 (M.op X5 X0)) (M.op X1 X1)) X1
       grind)
    | exact superpose eq3358 eq7129
    | exact resolve eq7129 eq3358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358 eq7129
  have eq7253 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7164 X0 X1 X2 X3 X4
       have i₂ := eq5408 (M.op X1 X1) X1 (M.op X2 (M.op X3 X0)) (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1)) X1
       grind)
    | exact superpose eq5408 eq7164
    | exact resolve eq7164 eq5408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408 eq7164
  have eq7259 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X1 X1))) (M.op X0 X1)) = (M.op (M.op X4 (M.op X5 X0)) (M.op X1 X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq7175 X0 X1 X2 X3 X4 X5
       have i₂ := eq21 X1 X1
       grind)
    | exact superpose eq21 eq7175
    | exact resolve eq7175 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq7175
  have eq7311 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X1))))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7253 X0 X1 X2 X3 X4
       have i₂ := eq5422 (M.op X1 X1) X1 (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq5422 eq7253
    | exact resolve eq7253 eq5422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5422 eq7253
  have eq7315 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X4 (M.op X5 X0)) (M.op X1 X1)) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq7259 X0 X1 x x X4 X5
       have i₂ := eq3659 (M.op X0 X1) X1 (M.op x x) X1
       grind)
    | exact superpose eq3659 eq7259
    | exact resolve eq7259 eq3659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7259
  have eq7334 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X1 (M.op X1 (M.op X1 X1))))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq7311 X0 X1 x x X4
       have i₂ := eq558 X1 X1 X0 x x
       grind)
    | exact superpose eq558 eq7311
    | exact resolve eq7311 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq7311
  have eq7341 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) (M.op X4 (M.op (M.op X1 (M.op X1 (M.op X1 X1))) X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq7334 X0 X1 X4
       have i₂ := eq7315 (M.op X1 (M.op X1 (M.op X1 X1))) X4 (M.op X1 X1) X0
       grind)
    | exact superpose eq7315 eq7334
    | exact resolve eq7334 eq7315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7315 eq7334
  have eq7344 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) (M.op X4 (M.op X1 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq7341 X0 X1 X4
       have i₂ := eq3659 X4 X1 X1 X1
       grind)
    | exact superpose eq3659 eq7341
    | exact resolve eq7341 eq3659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659 eq7341
  have eq48966 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (M.op (τ X0) (τ X0)))) = (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2029 (τ X1) (τ X0)
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq2029
    | (have j0 := eq2029 (M.op (τ X0) (τ X0)) (τ (k X0 X1))
       grind)
    | exact resolve eq2029 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq2029
  have eq49035 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (M.op (τ X0) (τ X0)))) = (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48966 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq48966
    | (have j0 := eq48966 X0 X1
       grind)
    | exact resolve eq48966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48966
  have eq49085 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (M.op (τ X0) (τ X0)))) = (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49035 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq49035
    | (have j0 := eq49035 X0 X1
       grind)
    | exact resolve eq49035 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49035
  have eq49116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (σ (M.op (τ X0) (τ X0)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49085 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq49085
    | (have j0 := eq49085 X0 X1
       grind)
    | exact resolve eq49085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49085
  have eq49141 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (σ (τ (M.op X0 X0)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49116 X0 X1
       have i₂ := eq1086 X0
       grind)
    | exact superpose eq1086 eq49116
    | (have j0 := eq49116 X0 X1
       grind)
    | exact resolve eq49116 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq49116
  have eq49163 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (σ (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq49141 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq49141
    | (have j0 := eq49141 X0 X1
       grind)
    | exact resolve eq49141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49141
  have eq49184 : ∀ X0 X1 : G, (σ X1) = (σ (σ (τ X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49163 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq49163
    | (have j0 := eq49163 X0 X1
       grind)
    | exact resolve eq49163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49163
  have eq49196 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49184 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49184
    | (have j0 := eq49184 X0 X1
       grind)
    | exact resolve eq49184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49184
  have eq272871 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq2413 X0
       grind)
    | exact superpose eq2413 eq48
    | exact resolve eq48 eq2413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq2413
  have eq308817 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 X2) (M.op (σ y) (M.op (σ x) (σ y)))))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1052 (σ x) (σ y) X0 X1 X2
       have i₂ := eq272871 (σ y)
       grind)
    | exact superpose eq272871 eq1052
    | exact resolve eq1052 eq272871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq272871
  have eq309286 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq308817 x x x
       have i₂ := eq3661 (σ y) (σ y) (M.op (σ x) (σ y)) x x x
       grind)
    | exact superpose eq3661 eq308817
    | exact resolve eq308817 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661 eq308817
  have eq309471 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq309286
       have i₂ := eq6221 (σ y) (σ x)
       grind)
    | exact superpose eq6221 eq309286
    | exact resolve eq309286 eq6221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6221 eq309286
  have eq309588 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq309471
       have i₂ := eq1088 y
       grind)
    | exact superpose eq1088 eq309471
    | exact resolve eq309471 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309471
  have eq338339 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq309588
       grind)
    | exact superpose eq309588 eq16
    | exact resolve eq16 eq309588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309588
  have eq338748 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq338339
       have r₂ := eq5211
       grind)
    | exact resolve eq338339 eq5211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5211 eq338339
  have eq372198 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2505 y x
       have i₂ := eq338748
       grind)
    | exact superpose eq338748 eq2505
    | exact resolve eq2505 eq338748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383702 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7344 X0 x y
       have i₂ := eq338748
       grind)
    | exact superpose eq338748 eq7344
    | exact resolve eq7344 eq338748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338748
  have eq384020 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq500 X1 X0 X2 X1 (M.op X2 X1) (M.op X0 X1)
       have i₂ := eq7344 X2 X1 (M.op (M.op X0 X1) (M.op X2 X1))
       grind)
    | exact superpose eq7344 eq500
    | exact resolve eq500 eq7344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq384524 : y = (M.op x (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq383702 x
       have i₂ := eq384020 x x y
       grind)
    | exact superpose eq384020 eq383702
    | exact resolve eq383702 eq384020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383702 eq384020
  have eq403749 : ∀ X0 : G, x = (M.op (M.op X0 y) y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq7344 X0 y x
       have i₂ := eq384524
       grind)
    | exact superpose eq384524 eq7344
    | exact resolve eq7344 eq384524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7344 eq384524
  have eq404204 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq403749 x
       have i₂ := eq2505 y x
       grind)
    | exact superpose eq2505 eq403749
    | exact resolve eq403749 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505 eq403749
  have eq445650 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2247 y
       have i₂ := eq404204
       grind)
    | exact superpose eq404204 eq2247
    | exact resolve eq2247 eq404204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247 eq404204
  have eq490794 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27 x y
       have i₂ := eq445650
       grind)
    | exact superpose eq445650 eq27
    | (have j0 := eq27 x y
       grind)
    | exact resolve eq27 eq445650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq490875 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq490794
  have eq749480 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49196 y x
       have i₂ := eq445650
       grind)
    | exact superpose eq445650 eq49196
    | (have j0 := eq49196 x (M.op y y)
       grind)
    | exact resolve eq49196 eq445650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49196 eq445650
  have eq749548 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq749480
  have eq749549 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq749548
  have eq1029014 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq749549
       have i₂ := eq372198
       grind)
    | exact superpose eq372198 eq749549
    | exact resolve eq749549 eq372198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372198 eq749549
  have eq1029438 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1029014
  have eq1155675 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq490875
       grind)
    | exact superpose eq490875 eq16
    | exact resolve eq16 eq490875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490875
  have eq1156343 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1155675
       have r₂ := eq1029438
       grind)
    | exact resolve eq1155675 eq1029438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029438 eq1155675
  have eq1175845 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1156343
       grind)
    | exact superpose eq1156343 eq10
    | exact resolve eq10 eq1156343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156343
  have eq1176290 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1175845
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1175845
    | exact resolve eq1175845 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175845
  have eq1176291 : x = y := by grind
  clear eq1176290
  have eq1197317 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1176291
       grind)
    | exact superpose eq1176291 eq16
    | exact resolve eq16 eq1176291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176291
  have eq1197318 : False := by grind
  exact eq1197318

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  have eq39 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k (M.op X0 X0) X0) X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq9
    | exact resolve eq9 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq25 X0 (k (M.op X0 X0) X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq25
    | exact resolve eq25 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq115 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq118 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq125 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq118 X0 X1
       have i₂ := eq25 X0 (M.op X1 X0)
       grind)
    | exact superpose eq25 eq118
    | exact resolve eq118 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq126 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq110
    | exact resolve eq110 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq168 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq24 X0 x x X3
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq171 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq24 X1 x x X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq235 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq126 (M.op X0 X0)
       grind)
    | exact superpose eq126 eq9
    | exact resolve eq9 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  clear eq235
  have eq248 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq244 X0
       have i₂ := eq115 (M.op X0 X0)
       grind)
    | exact superpose eq115 eq244
    | exact resolve eq244 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq251 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    grind
  clear eq248
  have eq253 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq251 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq251
    | exact resolve eq251 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq509 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (k (M.op X1 X1) X1) (M.op X1 (k (k (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (k (M.op X0 X0) X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq39
    | exact resolve eq39 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq39
  have eq539 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (k (M.op X1 X1) X1) (M.op X1 (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq509 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq509
    | exact resolve eq509 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq555 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (k (M.op X1 X1) X1) (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq125 X0 X0
       grind)
    | exact superpose eq125 eq539
    | exact resolve eq539 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq539
  have eq568 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (k (M.op X1 X1) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 X1
       have i₂ := eq253 X0
       grind)
    | exact superpose eq253 eq555
    | exact resolve eq555 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq555
  have eq577 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1
       have i₂ := eq115 X1
       grind)
    | exact superpose eq115 eq568
    | exact resolve eq568 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq762 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq171 X0 X0 X0
       grind)
    | exact superpose eq171 eq9
    | exact resolve eq9 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq168 (M.op x (M.op x x)) x
       have i₂ := eq171 x x x
       grind)
    | exact superpose eq171 eq168
    | exact resolve eq168 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq171
  have eq1241 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op (σ X0) (σ X1)) (M.op X2 X2))) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq58 X1 X0
       grind)
    | (have i₁ := eq9 X0 (σ X0) (σ X1)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq9
    | (have j1 := eq58 X1 X0
       grind)
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1243 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq58 X1 X0
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq58 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq13 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1298 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1243 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1299 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1321 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1299 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1299
    | (have j0 := eq1299 X0 X1
       grind)
    | exact resolve eq1299 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1401 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq780 X2 X3
       have i₂ := eq762 X2 X0 X1
       grind)
    | exact superpose eq762 eq780
    | exact resolve eq780 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq780
  have eq9318 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 X0) (M.op (M.op X0 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1401 (M.op X3 X0) (M.op X3 (M.op X3 X3)) X2 X1
       have i₂ := eq577 X0 X3
       grind)
    | exact superpose eq577 eq1401
    | exact resolve eq1401 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq1401
  have eq22614 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) ≠ (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1295 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1295
    | exact resolve eq1295 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq22629 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22614 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22614
    | (have j0 := eq22614 X0 X1
       grind)
    | exact resolve eq22614 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22614
  have eq22631 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22629 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22629
    | (have j0 := eq22629 X0 X1
       grind)
    | exact resolve eq22629 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22629
  have eq23281 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1321
    | exact resolve eq1321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq23617 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23281 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq23281
    | (have j0 := eq23281 X0 X1
       grind)
    | exact resolve eq23281 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23281
  have eq23640 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23617 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq23617
    | (have j0 := eq23617 X0 X1
       grind)
    | exact resolve eq23617 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23617
  have eq39549 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ X1) ∨ (M.op (σ X1) (M.op (M.op (σ X1) X0) (M.op X2 X2))) = X2 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1241 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1241
    | exact resolve eq1241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq40004 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op (σ X1) X0) (M.op X2 X2))) = X2 ∨ (M.op X0 X0) = (σ X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39549 X0 X1 X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq39549
    | (have j0 := eq39549 X0 X1 X2
       grind)
    | exact resolve eq39549 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq39549
  have eq349463 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq23640 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353501 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22631 X0 X1
       have i₂ := eq23640 X0 X1
       grind)
    | exact superpose eq23640 eq22631
    | (have j0 := eq22631 X0 X1
       have j1 := eq23640 X0 X1
       grind)
    | (have r₁ := eq22631 (σ X1) X1
       have r₂ := eq23640 (σ X1) X1
       grind)
    | exact resolve eq22631 eq23640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22631 eq23640
  have eq353525 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq353501 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353501
  have eq353528 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq353525 X0 X1
       have j1 := eq349463 X1 X0
       grind)
    | (have r₁ := eq353525 X1 X0
       have r₂ := eq349463 X0 X1
       grind)
    | (have r₁ := eq353525 (σ X0) X0
       have r₂ := eq349463 X0 (σ X0)
       grind)
    | exact resolve eq353525 eq349463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349463 eq353525
  have eq671164 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40004 X0 X1 (M.op (M.op X0 (M.op X0 X0)) X0)
       have i₂ := eq9318 X0 (σ X1) X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq9318 eq40004
    | (have j0 := eq40004 X0 X1 x
       grind)
    | exact resolve eq40004 eq9318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9318 eq40004
  have eq673720 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq671164 X0 X1
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq671164
    | (have j0 := eq671164 X0 X1
       grind)
    | exact resolve eq671164 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq671164
  have eq674042 : ∀ X0 X1 : G, (M.op X0 X0) = (σ X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq673720 X0 X1
       have j1 := eq353528 X0 X1
       grind)
    | (have r₁ := eq673720 X0 X1
       have r₂ := eq353528 X0 X1
       grind)
    | (have r₁ := eq673720 (σ X1) X1
       have r₂ := eq353528 (σ X1) X1
       grind)
    | exact resolve eq673720 eq353528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353528 eq673720
  have eq674592 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0
       have i₂ := eq674042 X0 X1
       grind)
    | exact superpose eq674042 eq115
    | (have j1 := eq674042 X1 X0
       grind)
    | exact resolve eq115 eq674042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq674042
  have eq676089 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq674592 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674592
  have eq678818 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq676089 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq676089
    | exact resolve eq676089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678898 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq676089 X1 (σ X0)
       grind)
    | exact superpose eq676089 eq15
    | exact resolve eq15 eq676089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676089
  have eq690639 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq678898 x y
       grind)
    | exact superpose eq678898 eq16
    | exact resolve eq16 eq678898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678898
  have eq691841 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq690639
       have i₂ := eq678818 y x
       grind)
    | exact superpose eq678818 eq690639
    | exact resolve eq690639 eq678818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678818 eq690639
  have eq691842 : False := by grind
  exact eq691842

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pyx_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq31
    | exact resolve eq31 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq58 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq58
    | exact resolve eq58 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq124 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq133 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq143 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq66 X1 X1
       grind)
    | exact superpose eq66 eq82
    | exact resolve eq82 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq82
  have eq286 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 (M.op X0 X0) X2 X1
       have i₂ := eq143 X0 X0
       grind)
    | exact superpose eq143 eq63
    | exact resolve eq63 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 (M.op X0 X1) X1 X3 X2
       have i₂ := eq286 X1 X1 X0
       grind)
    | exact superpose eq286 eq63
    | exact resolve eq63 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq347 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1 x x
       have i₂ := eq63 X1 X1 x x
       grind)
    | exact superpose eq63 eq338
    | exact resolve eq338 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq338
  have eq352 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq133
    | (have j0 := eq133 (σ (k X0 X1)) (σ X1)
       grind)
    | exact resolve eq133 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq399 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq395 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq395 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq395 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq395 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq557 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X1
       have i₂ := eq399 X0 X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq399 (M.op X0 X1) X1
       grind)
    | exact superpose eq399 eq31
    | (have j1 := eq399 X0 X1
       grind)
    | exact resolve eq31 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq570 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1
       have i₂ := eq399 X0 X1
       grind)
    | (have i₁ := eq60 X0
       have i₂ := eq399 (M.op X0 X0) X1
       grind)
    | exact superpose eq399 eq60
    | (have j1 := eq399 X0 X1
       grind)
    | exact resolve eq60 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1066 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1381 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X1
       have i₂ := eq557 X0 X1
       grind)
    | (have i₁ := eq570 X0 X0
       have i₂ := eq557 X0 X1
       grind)
    | exact superpose eq557 eq570
    | (have j0 := eq570 X0 X1
       have j1 := eq557 X0 X1
       grind)
    | exact resolve eq570 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq570
  have eq1434 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq2038 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 X0)
       have i₂ := eq143 X0 X0
       grind)
    | exact superpose eq143 eq62
    | exact resolve eq62 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq143
  have eq2085 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2038 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq2038
    | exact resolve eq2038 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq2038
  have eq2107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2085 X0
       have i₂ := eq1434 X0 X0
       grind)
    | exact superpose eq1434 eq2085
    | (have j1 := eq1434 X0 X0
       grind)
    | exact resolve eq2085 eq1434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434 eq2085
  have eq2121 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2107 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107
  have eq2137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2121 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2121
    | exact resolve eq2121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2142 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2137 X0
       have i₂ := eq2121 X0
       grind)
    | exact superpose eq2121 eq2137
    | exact resolve eq2137 eq2121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121 eq2137
  have eq2225 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq347 (σ X0) (σ X0)
       have i₂ := eq2142 X0
       grind)
    | exact superpose eq2142 eq347
    | exact resolve eq347 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5369 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq2142 X1
       grind)
    | exact superpose eq2142 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq5370 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5369 X0 X1
       have i₂ := eq2142 X1
       grind)
    | exact superpose eq2142 eq5369
    | (have j0 := eq5369 X0 X1
       grind)
    | exact resolve eq5369 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5369
  have eq6046 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 X1
       have i₂ := eq2142 X1
       grind)
    | exact superpose eq2142 eq1066
    | (have j0 := eq1066 X0 X1
       grind)
    | exact resolve eq1066 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq6047 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6046 X0 X1
       have i₂ := eq2142 X1
       grind)
    | exact superpose eq2142 eq6046
    | (have j0 := eq6046 X0 X1
       grind)
    | exact resolve eq6046 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142 eq6046
  have eq6048 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6047 X0 X1
       have j1 := eq5370 X0 X1
       grind)
    | (have r₁ := eq6047 X0 X1
       have r₂ := eq5370 X0 X1
       grind)
    | (have r₁ := eq6047 X0 X1
       have r₂ := eq5370 (k X0 X1) X1
       grind)
    | exact resolve eq6047 eq5370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5370 eq6047
  have eq6229 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq6048 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq6048 X0 X1
       grind)
    | exact superpose eq6048 eq10
    | (have j1 := eq6048 X0 X1
       grind)
    | exact resolve eq10 eq6048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6048
  have eq6301 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6229 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6229
    | (have j0 := eq6229 X0 X1
       grind)
    | exact resolve eq6229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6229
  have eq6712 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6301 x y
       grind)
    | exact superpose eq6301 eq16
    | (have j1 := eq6301 x y
       grind)
    | exact resolve eq16 eq6301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6301
  have eq6947 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6712
       have i₂ := eq399 x y
       grind)
    | exact superpose eq399 eq6712
    | (have j1 := eq399 x y
       grind)
    | exact resolve eq6712 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq6712
  have eq6961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq6947
  have eq6962 : x = (M.op y y) := by grind
  clear eq6961
  have eq6990 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2225 y
       have i₂ := eq6962
       grind)
    | exact superpose eq6962 eq2225
    | exact resolve eq2225 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq7015 : x = (M.op x y) := by
    first
    | (have i₁ := eq347 y y
       have i₂ := eq6962
       grind)
    | exact superpose eq6962 eq347
    | exact resolve eq347 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq6962
  have eq8268 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6990
       grind)
    | exact superpose eq6990 eq16
    | exact resolve eq16 eq6990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6990
  have eq8314 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq8268
       have i₂ := eq7015
       grind)
    | exact superpose eq7015 eq8268
    | exact resolve eq8268 eq7015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7015 eq8268
  have eq8315 : False := by grind
  exact eq8315

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq178
    | exact resolve eq178 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq174
    | exact resolve eq174 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq595 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq595
    | exact resolve eq595 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq615 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq177 X0 (k (M.op X0 X0) X0)
       have i₂ := eq605 X0
       grind)
    | exact superpose eq605 eq177
    | exact resolve eq177 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (k (M.op X0 X0) X0) X0
       have i₂ := eq605 X0
       grind)
    | exact superpose eq605 eq16
    | exact resolve eq16 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq658 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq944 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq181 eq177
    | exact resolve eq177 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq946 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq985 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq944 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq944
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq944 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1009 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq985 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1404 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq600 (M.op X0 X0) (M.op X1 (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq16 eq600
    | exact resolve eq600 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1543 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq601 (M.op X0 X0) (M.op X1 (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq16 eq601
    | exact resolve eq601 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq1564 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1543 X0 x
       have i₂ := eq1404 X0 x
       grind)
    | exact superpose eq1404 eq1543
    | exact resolve eq1543 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404 eq1543
  have eq1844 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq39
    | exact resolve eq39 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq1845 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1844
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1844
    | exact resolve eq1844 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq1847 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1845
    | exact resolve eq1845 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq3230 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq617 X0 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq617
    | exact resolve eq617 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq3413 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq946 X0 X1 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq946
    | exact resolve eq946 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3444 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq946 X0 X0 X0
       grind)
    | exact superpose eq946 eq16
    | exact resolve eq16 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3445 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq174 (M.op X0 (M.op X0 X0))
       have i₂ := eq946 X0 X0 X0
       grind)
    | exact superpose eq946 eq174
    | exact resolve eq174 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq3449 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq179 (M.op x (M.op x x))
       have i₂ := eq946 x x x
       grind)
    | exact superpose eq946 eq179
    | exact resolve eq179 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq3492 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = (k X0 (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3449 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq3449
    | exact resolve eq3449 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449
  have eq3525 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3492 X0
       have i₂ := eq615 X0
       grind)
    | exact superpose eq615 eq3492
    | exact resolve eq3492 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq3492
  have eq3572 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq3445 X0
       grind)
    | exact superpose eq3445 eq179
    | exact resolve eq179 eq3445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445
  have eq4166 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq605 X0
       have i₂ := eq3572 X0
       grind)
    | exact superpose eq3572 eq605
    | exact resolve eq605 eq3572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq3572
  have eq4214 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1564 eq4166
    | exact resolve eq4166 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564 eq4166
  have eq4462 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op (M.op X2 X1) (k X0 X0))
       have i₂ := eq712 X0 X1 X2
       grind)
    | exact superpose eq712 eq177
    | (have j1 := eq712 X0 X1 X2
       grind)
    | exact resolve eq177 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq4473 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1009 eq4462
    | (have j0 := eq4462 X0 x x
       have j1 := eq1009 X0 x
       grind)
    | exact resolve eq4462 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009 eq4462
  have eq4487 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4473 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq4473 x
       have r₂ := eq13 (k x x) x
       grind)
    | (have r₁ := eq4473 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq4473 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq4473 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4473
  have eq4517 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq4487 X0
       grind)
    | exact superpose eq4487 eq175
    | exact resolve eq175 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq4520 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq4487 X0
       grind)
    | exact superpose eq4487 eq179
    | exact resolve eq179 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq4569 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq4487 (M.op X0 X1)
       grind)
    | exact superpose eq4487 eq177
    | exact resolve eq177 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq4804 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq4517 eq4214
    | exact resolve eq4214 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214 eq4517
  have eq5346 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4804 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq4804
    | exact resolve eq4804 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36057 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 X0) (k X0 (k (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3413 (k (M.op X0 X0) X0) X1
       have i₂ := eq3230 X0
       grind)
    | exact superpose eq3230 eq3413
    | exact resolve eq3413 eq3230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230 eq3413
  have eq36114 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36057 X0 X1
       have i₂ := eq3525 X0
       grind)
    | exact superpose eq3525 eq36057
    | exact resolve eq36057 eq3525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3525 eq36057
  have eq36162 : ∀ X0 X1 : G, (k (k X0 X0) X0) = (M.op (M.op X1 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36114 X0 X1
       have i₂ := eq4487 X0
       grind)
    | exact superpose eq4487 eq36114
    | exact resolve eq36114 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36114
  have eq36803 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 (M.op X1 X0)
       have i₂ := eq3444 X0 X0 X1
       grind)
    | exact superpose eq3444 eq600
    | exact resolve eq600 eq3444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq36882 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq600 eq36803
    | exact resolve eq36803 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq36803
  have eq37200 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq36882 X0 X1
       have i₂ := eq4487 X0
       grind)
    | exact superpose eq4487 eq36882
    | exact resolve eq36882 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36882
  have eq94550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1847 eq684
    | exact resolve eq684 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq1847
  have eq94561 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq94550
       have r₂ := eq27
       grind)
    | exact resolve eq94550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94550
  have eq94569 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94561
       have i₂ := eq4487 sF2
       grind)
    | exact superpose eq4487 eq94561
    | exact resolve eq94561 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94561
  have eq94575 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq94569
       have i₂ := eq4487 x
       grind)
    | exact superpose eq4487 eq94569
    | exact resolve eq94569 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94569
  have eq94614 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq94575 eq4804
    | exact resolve eq4804 eq94575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94575
  have eq94677 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq94614
  have eq94753 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq94677 eq37200
    | exact resolve eq37200 eq94677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94758 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq94677 eq94753
    | exact resolve eq94753 eq94677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94677 eq94753
  have eq94829 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq94758 eq97
    | exact resolve eq97 eq94758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq94758
  have eq94985 : y = (k x x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq94829
    | exact resolve eq94829 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq94829
  have eq94986 : y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq94985
  have eq95070 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4804 x
       have i₂ := eq94986
       grind)
    | exact superpose eq94986 eq4804
    | exact resolve eq4804 eq94986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804 eq94986
  have eq95133 : y = (M.op y x) := by grind
  clear eq95070
  have eq95205 : (k x x) = (M.op y x) := by
    first
    | (have i₁ := eq37200 x y
       have i₂ := eq95133
       grind)
    | exact superpose eq95133 eq37200
    | exact resolve eq37200 eq95133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37200
  have eq95210 : y = (k x x) := by
    first
    | (have i₁ := eq95205
       have i₂ := eq95133
       grind)
    | exact superpose eq95133 eq95205
    | exact resolve eq95205 eq95133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95133 eq95205
  have eq95273 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq95210
       grind)
    | exact superpose eq95210 eq39
    | exact resolve eq39 eq95210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95282 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq4520 x
       have i₂ := eq95210
       grind)
    | exact superpose eq95210 eq4520
    | exact resolve eq4520 eq95210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4520
  have eq95312 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5346 x
       have i₂ := eq95210
       grind)
    | exact superpose eq95210 eq5346
    | exact resolve eq5346 eq95210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346 eq95210
  have eq95404 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq95312
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95312
    | exact resolve eq95312 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95312
  have eq95419 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq95282
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95282
    | exact resolve eq95282 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq95282
  have eq95428 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq95273
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95273
    | exact resolve eq95273 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95273
  have eq95458 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq95404
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95404
    | exact resolve eq95404 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95404
  have eq95478 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq95428
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95428
    | exact resolve eq95428 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95428
  have eq95694 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq95419
       grind)
    | exact superpose eq95419 eq39
    | exact resolve eq39 eq95419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq95419
  have eq95697 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq95694
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95694
    | exact resolve eq95694 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq95694
  have eq95701 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq95697
    | exact resolve eq95697 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq95697
  have eq95734 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq95458 eq4569
    | exact resolve eq4569 eq95458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4569
  have eq95741 : (k (k (σ x) (σ x)) (σ x)) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | exact superpose eq95458 eq36162
    | exact resolve eq36162 eq95458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36162 eq95458
  have eq95750 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq95478 eq95741
    | exact resolve eq95741 eq95478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95478 eq95741
  have eq95753 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq95734
    | exact resolve eq95734 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq95734
  have eq95777 : (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq95750
       have i₂ := eq4487 sF3
       grind)
    | exact superpose eq4487 eq95750
    | exact resolve eq95750 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4487 eq95750
  have eq95797 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq95753 eq95777
    | exact resolve eq95777 eq95753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95753 eq95777
  have eq95813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95701 eq95797
    | exact resolve eq95797 eq95701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95701 eq95797
  have eq95822 : False := by grind
  exact eq95822

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
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
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
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
  have eq175 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq176 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq176 (M.op sF4 sF4)
       have i₂ := eq16 sF4 sF4 sF4
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op (σ x) (σ y)) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq182 eq175
    | exact resolve eq175 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (τ X0) X1) X2
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq571 : ∀ X0 : G, (M.op y (M.op (M.op x y) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq175
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq175 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq579 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq572 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq572 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq603 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq579
       grind)
    | exact superpose eq579 eq41
    | exact resolve eq41 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq603
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq603
    | exact resolve eq603 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq606 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq604
    | exact resolve eq604 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq613 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq596 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq596
    | (have j0 := eq596 (σ X0)
       grind)
    | exact resolve eq596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq606 eq585
    | exact resolve eq585 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq623 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq616
       have r₂ := eq27
       grind)
    | exact resolve eq616 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq628 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq623 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op X0 X0))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq623 eq16
    | exact resolve eq16 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq623 eq176
    | exact resolve eq176 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : (σ x) = (M.op y (M.op (M.op x y) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq623 eq175
    | exact resolve eq175 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq628 eq98
    | exact resolve eq98 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq652 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq646
    | exact resolve eq646 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq658 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq178 X0 X0
       grind)
    | exact superpose eq178 eq658
    | (have j0 := eq658 X0
       grind)
    | exact resolve eq658 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq660 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq601 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq601
    | (have j0 := eq601 (σ X0) X1
       grind)
    | exact resolve eq601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq666 : x ≠ y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq596 x
       have i₂ := eq652
       grind)
    | exact superpose eq652 eq596
    | (have j0 := eq596 x
       grind)
    | exact resolve eq596 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq623 eq630
    | exact resolve eq630 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq630 (M.op sF3 sF3)
       have i₂ := eq16 sF3 sF3 sF3
       grind)
    | exact superpose eq16 eq630
    | exact resolve eq630 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq680
  have eq691 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq682
    | exact resolve eq682 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq696 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq691 eq630
    | exact resolve eq630 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq691 eq176
    | exact resolve eq176 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq691 eq16
    | exact resolve eq16 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by grind
  clear eq696
  have eq703 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq182 eq698
    | exact resolve eq698 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq708 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq688 eq188
    | exact resolve eq188 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq691 eq708
    | exact resolve eq708 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq716 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq702 eq712
    | exact resolve eq712 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq712
  have eq729 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq716 eq631
    | exact resolve eq631 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq733 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq729
  have eq771 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq733 eq703
    | exact resolve eq703 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq779 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq771
  have eq1119 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = (M.op X1 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 (k X0 X1) (M.op X1 (k X0 X1))
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1156 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq178 X0 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1160 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1163 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 X3
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1254 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1255 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq177 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 (M.op X1 X1) X1 X2 X1
       have i₂ := eq178 X1 X1
       grind)
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1271 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1272 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1273 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq177 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1275 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq177 X1 x x X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1277 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq178 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq177 X0 x x X3
       grind)
    | exact superpose eq177 eq178
    | exact resolve eq178 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1283 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1273 X0 X1
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq1273
    | exact resolve eq1273 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1284 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1272 X0 X1
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq1272
    | exact resolve eq1272 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1285 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1271 X0 X1 X2 X3
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq1271
    | exact resolve eq1271 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1294 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1255 X0 X1 X2 X3 X4
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq1255
    | exact resolve eq1255 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1297 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1284 X0 X1
       have i₂ := eq1283 X0 X1
       grind)
    | exact superpose eq1283 eq1284
    | exact resolve eq1284 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1298 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1285 X0 X1 X2 X3
       have i₂ := eq1283 X0 X1
       grind)
    | exact superpose eq1283 eq1285
    | exact resolve eq1285 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1304 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1294 X0 X1 X2 X3 X4
       have i₂ := eq1283 X0 X1
       grind)
    | exact superpose eq1283 eq1294
    | exact resolve eq1294 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq1294
  have eq1780 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq188 eq701
    | exact resolve eq701 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq701
  have eq1932 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq182 eq1780
    | exact resolve eq1780 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq1944 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (σ x)) (σ x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq733 eq1932
    | exact resolve eq1932 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq3707 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq623 eq659
    | exact resolve eq659 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3719 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq3707
    | exact resolve eq3707 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3707
  have eq3731 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3719 eq91
    | exact resolve eq91 eq3719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq3719
  have eq3739 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq3731
    | exact resolve eq3731 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3731
  have eq3742 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq579 eq3739
    | exact resolve eq3739 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579 eq3739
  have eq3772 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq659 x
       have i₂ := eq3742
       grind)
    | exact superpose eq3742 eq659
    | exact resolve eq659 eq3742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq3776 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq178 x x
       have i₂ := eq3742
       grind)
    | exact superpose eq3742 eq178
    | exact resolve eq178 eq3742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3742
  have eq3779 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3776
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3776
    | exact resolve eq3776 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq3780 : y = (M.op x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3772
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3772
    | exact resolve eq3772 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3772
  have eq3781 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3780
  have eq3827 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq3779
       grind)
    | exact superpose eq3779 eq28
    | exact resolve eq28 eq3779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3779
  have eq3844 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3827
  have eq3848 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq3781
       grind)
    | exact superpose eq3781 eq36
    | exact resolve eq36 eq3781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3781
  have eq3854 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3848
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3848
    | exact resolve eq3848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3848
  have eq3859 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3844
       grind)
    | exact superpose eq3844 eq41
    | exact resolve eq41 eq3844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3844
  have eq3866 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3859
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3859
    | exact resolve eq3859 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859
  have eq3868 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3866
    | exact resolve eq3866 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3866
  have eq3873 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3854 eq585
    | exact resolve eq585 eq3854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq3854
  have eq3878 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3873
  have eq3920 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3878 eq178
    | exact resolve eq178 eq3878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3878
  have eq3935 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3920
    | exact resolve eq3920 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920
  have eq3945 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3935 eq176
    | exact resolve eq176 eq3935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3953 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3935 eq28
    | exact resolve eq28 eq3935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq3970 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3953
  have eq3971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3868 eq3970
    | exact resolve eq3970 eq3868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868 eq3970
  have eq3972 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq182 eq3945
    | exact resolve eq3945 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq3945
  have eq3974 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3971
       have r₂ := eq27
       grind)
    | exact resolve eq3971 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3971
  have eq3976 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3974 eq27
    | exact resolve eq27 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3977 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op X0 X0))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3974 eq176
    | exact resolve eq176 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3990 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3974 eq716
    | exact resolve eq716 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq3991 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3974 eq733
    | exact resolve eq733 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4016 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3991 eq3990
    | exact resolve eq3990 eq3991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3990
  have eq4133 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 X0)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3977 (M.op X1 X0)
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq3977
    | exact resolve eq3977 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5078 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3991 eq688
    | exact resolve eq688 eq3991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq5084 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3991 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq3991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991
  have eq5136 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq5078
  have eq5160 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5084 X0
       grind)
    | (have r₁ := eq5084 X0
       have r₂ := eq4016
       grind)
    | exact resolve eq5084 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5084
  have eq5171 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4016 eq5160
    | exact resolve eq5160 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160
  have eq7923 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (M.op (σ y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq180 eq3977
    | exact resolve eq3977 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq14504 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5171 eq5136
    | exact resolve eq5136 eq5171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14527 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq14504
  have eq15568 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq1275 X0 X0 X0
       grind)
    | exact superpose eq1275 eq16
    | exact resolve eq16 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15570 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq176 (M.op X0 (M.op X0 X0))
       have i₂ := eq1275 X0 X0 X0
       grind)
    | exact superpose eq1275 eq176
    | exact resolve eq176 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15591 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3977 (M.op X0 (M.op X0 X0))
       have i₂ := eq1275 X0 X0 X0
       grind)
    | exact superpose eq1275 eq3977
    | exact resolve eq3977 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15771 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14527 eq142
    | exact resolve eq142 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq14527
  have eq15789 : y = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq15771
    | exact resolve eq15771 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771
  have eq15793 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15789
       have i₂ := eq28 x x
       grind)
    | exact superpose eq28 eq15789
    | (have j1 := eq28 x x
       grind)
    | exact resolve eq15789 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15814 : x = (M.op x (M.op x y)) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1156 x
       have i₂ := eq15789
       grind)
    | exact superpose eq15789 eq1156
    | exact resolve eq1156 eq15789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15789
  have eq15866 : x = (k x x) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15814
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15814
    | exact resolve eq15814 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15814
  have eq15877 : y = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq596 x
       grind)
    | (have r₁ := eq15793
       have r₂ := eq596 x
       grind)
    | exact resolve eq15793 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15793
  have eq16087 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq596 x
       have i₂ := eq15866
       grind)
    | exact superpose eq15866 eq596
    | (have j0 := eq596 x
       grind)
    | (have r₁ := eq596 x
       have r₂ := eq15866
       grind)
    | exact resolve eq596 eq15866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15866
  have eq16089 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq16087
  have eq16118 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq15877
       grind)
    | exact superpose eq15877 eq40
    | exact resolve eq40 eq15877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16122 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq596 x
       have i₂ := eq15877
       grind)
    | exact superpose eq15877 eq596
    | (have j0 := eq596 x
       grind)
    | exact resolve eq596 eq15877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16125 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq16122
  have eq16133 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16118
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16118
    | exact resolve eq16118 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16118
  have eq16137 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16133
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16133
    | exact resolve eq16133 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16133
  have eq16165 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16089 eq178
    | exact resolve eq178 eq16089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16089
  have eq16207 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq16165
    | (have j1 := eq28 x x
       grind)
    | exact resolve eq16165 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16165
  have eq16212 : y = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15877 eq16207
    | exact resolve eq16207 eq15877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15877 eq16207
  have eq16272 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X1 X0) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq16137 eq573
    | (have j0 := eq573 (σ x) X1 x
       grind)
    | exact resolve eq573 eq16137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq16281 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16272 x x
       have i₂ := eq15568 sF3 x x
       grind)
    | exact superpose eq15568 eq16272
    | exact resolve eq16272 eq15568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15568 eq16272
  have eq16285 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq5136 eq16281
    | exact resolve eq16281 eq5136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5136 eq16281
  have eq16316 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16212 eq178
    | exact resolve eq178 eq16212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16212
  have eq16363 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16316
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16316
    | exact resolve eq16316 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16316
  have eq16552 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq16363
       grind)
    | exact superpose eq16363 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq16363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16363
  have eq16588 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq16552
  have eq16620 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq16588
       grind)
    | exact superpose eq16588 eq41
    | exact resolve eq41 eq16588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq16588
  have eq16627 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16620
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16620
    | exact resolve eq16620 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16620
  have eq16629 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq16627
    | exact resolve eq16627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16627
  have eq16682 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1156 X0
       have i₂ := eq15591 X0
       grind)
    | (have i₁ := eq1156 (σ y)
       have i₂ := eq15591 (σ y)
       grind)
    | exact superpose eq15591 eq1156
    | exact resolve eq1156 eq15591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16683 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1275 X0 X1 X0
       have i₂ := eq15591 X0
       grind)
    | (have i₁ := eq1275 (σ y) X1 (σ y)
       have i₂ := eq15591 (σ y)
       grind)
    | exact superpose eq15591 eq1275
    | exact resolve eq1275 eq15591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16690 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) X0)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1160 X0 X0
       have i₂ := eq15591 X0
       grind)
    | (have i₁ := eq1160 (σ y) (σ y)
       have i₂ := eq15591 (σ y)
       grind)
    | exact superpose eq15591 eq1160
    | exact resolve eq1160 eq15591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq16725 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (σ y) (M.op (σ y) (M.op X0 X1)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X0
       have i₂ := eq15591 (M.op X0 X1)
       grind)
    | exact superpose eq15591 eq16
    | exact resolve eq16 eq15591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16809 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) X0)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3974 eq16690
    | exact resolve eq16690 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16690
  have eq56332 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X0 X0))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16683 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq1275 X0 X0 X0
       grind)
    | exact superpose eq1275 eq16683
    | exact resolve eq16683 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56373 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16683 X0 X0
       have i₂ := eq15591 X0
       grind)
    | (have i₁ := eq16683 (σ y) (σ y)
       have i₂ := eq15591 (σ y)
       grind)
    | exact superpose eq15591 eq16683
    | exact resolve eq16683 eq15591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15591
  have eq56702 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq56373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56373
  have eq56819 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56702 X0
       have i₂ := eq178 sF3 (M.op sF3 X0)
       grind)
    | exact superpose eq178 eq56702
    | exact resolve eq56702 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56702
  have eq56847 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4133 eq56332
    | exact resolve eq56332 eq4133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133 eq56332
  have eq63601 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op (σ y) (M.op (σ y) X0)))) (M.op X0 X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq16809 eq16683
    | exact resolve eq16683 eq16809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63660 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) (M.op (σ y) (M.op (σ y) (M.op X0 X0)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16809 eq16725
    | exact resolve eq16725 eq16809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16725 eq16809
  have eq63667 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) (M.op (σ y) (M.op (σ y) (M.op X0 X0)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq63660 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63660
  have eq63691 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op (σ y) (M.op (σ y) X0)))) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq63601 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63601
  have eq63776 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (σ y) (M.op (σ y) (M.op (σ y) X0))) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3977 eq63667
    | exact resolve eq63667 eq3977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63667
  have eq63800 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (M.op (σ y) X0) (M.op (σ y) (M.op (σ y) X0)))) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq63691 X0 X1
       have i₂ := eq178 sF3 (M.op sF3 X0)
       grind)
    | exact superpose eq178 eq63691
    | exact resolve eq63691 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63691
  have eq63958 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq56819 eq63800
    | exact resolve eq63800 eq56819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63800
  have eq66676 : (M.op y (M.op y y)) = (M.op (M.op x y) (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56847 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56847
    | (have j0 := eq56847 y x
       grind)
    | exact resolve eq56847 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67325 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op x y) (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66676
       have i₂ := eq15570 y
       grind)
    | exact superpose eq15570 eq66676
    | exact resolve eq66676 eq15570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15570 eq66676
  have eq67562 : (M.op (M.op x y) (M.op y y)) = (M.op (σ y) (M.op (σ y) y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3974 eq67325
    | exact resolve eq67325 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67325
  have eq67895 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y y)) (M.op (M.op x y) (M.op y y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq67562 eq16683
    | exact resolve eq16683 eq67562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67562
  have eq67991 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y y)) (M.op (M.op x y) (M.op y y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq67895 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67895
  have eq70900 : (M.op (σ x) (σ x)) = (k (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ x)))) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63776 eq5171
    | exact resolve eq5171 eq63776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171 eq63776
  have eq70990 : (M.op (σ x) (σ x)) = (k (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ x)))) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq70900
  have eq71116 : (σ y) = (k (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ x)))) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq623 eq70990
    | exact resolve eq70990 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq70990
  have eq71225 : (σ y) = (k (M.op (σ y) (M.op (σ y) (σ y))) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq779 eq71116
    | exact resolve eq71116 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq71116
  have eq71306 : (σ y) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq691 eq71225
    | exact resolve eq71225 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq71225
  have eq71366 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq733 eq71306
    | exact resolve eq71306 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq71306
  have eq71396 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq16137 eq71366
    | exact resolve eq71366 eq16137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71366
  have eq71444 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq71396 eq596
    | (have j0 := eq596 (σ x)
       grind)
    | exact resolve eq596 eq71396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq72944 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq56819 eq1163
    | exact resolve eq1163 eq56819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56819
  have eq73002 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1163 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq1163 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq1163 eq1163
    | exact resolve eq1163 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87311 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (σ y) (M.op (σ y) X0))) = (M.op (M.op X0 X0) (M.op (σ y) (M.op (σ y) X0))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq56847 (M.op X0 X0) X1
       have i₂ := eq63958 X0 X0
       grind)
    | exact superpose eq63958 eq56847
    | exact resolve eq56847 eq63958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56847
  have eq87387 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op (σ y) (M.op (σ y) X0))) = (M.op (M.op X0 X0) (M.op (σ y) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq87311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87311
  have eq87670 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16683 eq87387
    | exact resolve eq87387 eq16683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16683 eq87387
  have eq90383 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op X0 X0) (M.op (σ y) (M.op (σ y) X0)))) (M.op (M.op X0 X0) (M.op (σ y) (M.op (σ y) X0)))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1262 (M.op X0 X0) X1 X2
       have i₂ := eq63958 X0 X0
       grind)
    | exact superpose eq63958 eq1262
    | exact resolve eq1262 eq63958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq63958
  have eq90561 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq87670 eq90383
    | exact resolve eq90383 eq87670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87670 eq90383
  have eq92997 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq176 eq90561
    | exact resolve eq90561 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90561
  have eq94682 : (M.op y y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq92997 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92997
    | (have j0 := eq92997 x y
       grind)
    | exact resolve eq92997 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92997
  have eq103493 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq183 eq1298
    | exact resolve eq1298 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq109315 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ y) X0)) (M.op (σ y) (M.op (σ y) X0))) = (M.op (M.op (M.op X2 X1) X0) (M.op (σ y) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X1 (M.op (M.op X2 X1) X0)
       have i₂ := eq72944 X0 X1 X2
       grind)
    | exact superpose eq72944 eq178
    | exact resolve eq178 eq72944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109984 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) (M.op (σ y) (M.op (σ y) X0))) = (M.op (M.op (M.op X2 X1) X0) (M.op (σ y) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109315 X0 X1 X2
       have i₂ := eq178 sF3 (M.op sF3 X0)
       grind)
    | exact superpose eq178 eq109315
    | exact resolve eq109315 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109315
  have eq110438 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ y) (M.op (σ y) X0))) = (M.op (M.op (M.op X2 X1) X0) (M.op (σ y) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109984 X2 X1 X2
       have i₂ := eq73002 sF3 sF3 X2
       grind)
    | exact superpose eq73002 eq109984
    | exact resolve eq109984 eq73002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73002 eq109984
  have eq110640 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) X0) (M.op (σ y) (M.op (σ y) X0))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq16682 eq110438
    | exact resolve eq110438 eq16682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16682 eq110438
  have eq116139 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq71396 eq1119
    | (have j0 := eq1119 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1119 eq71396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116351 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq116139
    | exact resolve eq116139 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116139
  have eq116392 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq3974 eq116351
    | exact resolve eq116351 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116351
  have eq120227 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op x y) (M.op y y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq67991 eq1277
    | exact resolve eq1277 eq67991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120448 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op x y) (M.op (M.op x y) y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq94682 eq120227
    | exact resolve eq120227 eq94682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120227
  have eq120827 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq120448 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120448
    | (have j0 := eq120448 x
       grind)
    | exact resolve eq120448 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120448
  have eq122586 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ y) (M.op (σ y) X1))) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq176 eq110640
    | exact resolve eq110640 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110640
  have eq126360 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq116392 eq122586
    | exact resolve eq122586 eq116392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116392
  have eq126361 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq126360
  have eq126443 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq16285 eq126361
    | exact resolve eq126361 eq16285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16285 eq126361
  have eq126485 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq126443
       have r₂ := eq71444
       grind)
    | exact resolve eq126443 eq71444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71444 eq126443
  have eq126563 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq126485 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq126485
       grind)
    | exact resolve eq13 eq126485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126485
  have eq126745 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq126563 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126563
  have eq128750 : (σ x) = (M.op (σ x) (M.op (σ x) (k (σ x) (σ x)))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq126745 eq1156
    | exact resolve eq1156 eq126745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126745
  have eq129206 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq71396 eq128750
    | exact resolve eq128750 eq71396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71396 eq128750
  have eq129309 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq129206
    | exact resolve eq129206 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129206
  have eq129376 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3974 eq129309
    | exact resolve eq129309 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129309
  have eq129416 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq129376
    | exact resolve eq129376 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129376
  have eq129527 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq129416 eq3974
    | exact resolve eq3974 eq129416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129416
  have eq129612 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq129527
  have eq129680 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq129612 eq32
    | exact resolve eq32 eq129612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129805 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq129612 eq16629
    | exact resolve eq16629 eq129612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16629 eq129612
  have eq130044 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq129805
  have eq130125 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq130044
       have r₂ := eq16125
       grind)
    | exact resolve eq130044 eq16125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16125 eq130044
  have eq130151 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq129680
    | exact resolve eq129680 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129680
  have eq130152 : y = (M.op x y) ∨ x = y := by grind
  clear eq130151
  have eq130169 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16137 eq130125
    | exact resolve eq130125 eq16137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16137 eq130125
  have eq130183 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq130169
       have r₂ := eq3976
       grind)
    | exact resolve eq130169 eq3976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976 eq130169
  have eq130188 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq130152
       grind)
    | exact superpose eq130152 eq175
    | exact resolve eq175 eq130152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130335 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq130183
       grind)
    | exact superpose eq130183 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq130183
       grind)
    | exact resolve eq13 eq130183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130387 : x = (M.op (σ y) (M.op (σ y) x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3977 x
       have i₂ := eq130183
       grind)
    | exact superpose eq130183 eq3977
    | exact resolve eq3977 eq130183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3977
  have eq130419 : ∀ X0 : G, (M.op x (M.op x (M.op X0 X0))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq130183
       grind)
    | exact superpose eq130183 eq16
    | exact resolve eq16 eq130183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130516 : x = (M.op (σ y) (M.op (σ y) x)) ∨ y = (M.op x y) := by grind
  clear eq130387
  have eq130519 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq130335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130335
  have eq132695 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) x)) = (M.op X1 (k (M.op X0 X1) x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq72944 x X1 X0
       have i₂ := eq130519 (M.op X0 X1)
       grind)
    | exact superpose eq130519 eq72944
    | exact resolve eq72944 eq130519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132710 : x = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq130183
       have i₂ := eq130519 x
       grind)
    | exact superpose eq130519 eq130183
    | exact resolve eq130183 eq130519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130183
  have eq132857 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq132710
  have eq132868 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) x)) = (M.op X1 (k (M.op X0 X1) x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq132695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132695
  have eq133063 : ∀ X0 X1 : G, x = (M.op X1 (k (M.op X0 X1) x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq130516 eq132868
    | exact resolve eq132868 eq130516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132868
  have eq133492 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq132857
       grind)
    | exact superpose eq132857 eq40
    | exact resolve eq40 eq132857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133530 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq133492
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq133492
    | exact resolve eq133492 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133492
  have eq140685 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq130188 (M.op X0 (M.op X0 X0))
       have i₂ := eq1275 X0 X0 X0
       grind)
    | exact superpose eq1275 eq130188
    | exact resolve eq130188 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130188
  have eq141057 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq130419 (M.op X0 (M.op X0 X0))
       have i₂ := eq1275 X0 X0 X0
       grind)
    | exact superpose eq1275 eq130419
    | exact resolve eq130419 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141062 : (M.op (M.op x y) (M.op y y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq67991 eq130419
    | exact resolve eq130419 eq67991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67991 eq130419
  have eq141257 : (M.op (M.op x y) (M.op y y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq141062
  have eq141316 : (M.op (M.op x y) (M.op y y)) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq141257
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq141257
    | exact resolve eq141257 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141257
  have eq141344 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq94682 eq141316
    | exact resolve eq141316 eq94682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94682 eq141316
  have eq141356 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130152 eq141344
    | exact resolve eq141344 eq130152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141344
  have eq141361 : (M.op x (M.op x y)) = (M.op (M.op x y) (k (M.op x y) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130519 eq141356
    | exact resolve eq141356 eq130519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141356
  have eq142985 : x = (M.op (M.op (M.op x y) (M.op (M.op x y) y)) (k y x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120827 eq133063
    | exact resolve eq133063 eq120827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120827 eq133063
  have eq143391 : x = (M.op (M.op (M.op x y) (M.op (M.op x y) y)) (k y x)) ∨ y = (M.op x y) := by grind
  clear eq142985
  have eq143713 : x = (M.op (M.op (M.op x y) (M.op (M.op x y) x)) (k x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130152 eq143391
    | exact resolve eq143391 eq130152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130152 eq143391
  have eq144008 : x = (M.op (M.op (M.op x y) (k (M.op x y) x)) (k x x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130519 eq143713
    | exact resolve eq143713 eq130519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143713
  have eq144168 : x = (M.op (M.op (M.op x y) (k (M.op x y) x)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq132857 eq144008
    | exact resolve eq144008 eq132857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132857 eq144008
  have eq144246 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq141361 eq144168
    | exact resolve eq144168 eq141361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144168
  have eq144439 : (M.op (M.op x y) x) = (M.op (σ y) (M.op (σ y) x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144246 eq72944
    | exact resolve eq72944 eq144246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72944 eq144246
  have eq144545 : (M.op (M.op x y) x) = (M.op (σ y) (M.op (σ y) x)) ∨ y = (M.op x y) := by grind
  clear eq144439
  have eq144577 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130516 eq144545
    | exact resolve eq144545 eq130516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130516 eq144545
  have eq144629 : x = (k (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144577 eq130519
    | exact resolve eq130519 eq144577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144577
  have eq144709 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq144629
  have eq150198 : (M.op x (M.op x y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144709 eq141361
    | exact resolve eq141361 eq144709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150209 : (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) = (M.op (k (M.op x y) x) (M.op x (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq141361 eq178
    | exact resolve eq178 eq141361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141361
  have eq150294 : (M.op x (M.op x y)) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq150198
  have eq150320 : (M.op (M.op x y) (M.op x (M.op x y))) = (M.op (k (M.op x y) x) (M.op x (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq150209
       have i₂ := eq178 x sF0
       grind)
    | exact superpose eq178 eq150209
    | exact resolve eq150209 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150209
  have eq150326 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130519 eq150294
    | exact resolve eq150294 eq130519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150294
  have eq150347 : (M.op (M.op x y) (M.op x (M.op x y))) = (M.op x (M.op x (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144709 eq150320
    | exact resolve eq150320 eq144709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150320
  have eq150351 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144709 eq150326
    | exact resolve eq150326 eq144709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150326
  have eq150367 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op x (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq141057 eq150347
    | exact resolve eq150347 eq141057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141057 eq150347
  have eq150379 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150351 eq150367
    | exact resolve eq150367 eq150351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150367
  have eq150385 : (k (M.op x y) x) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130519 eq150379
    | exact resolve eq150379 eq130519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150379
  have eq150390 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144709 eq150385
    | exact resolve eq150385 eq144709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144709 eq150385
  have eq150485 : (M.op x y) = (M.op x (M.op (σ y) (M.op (σ y) (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150351 eq122586
    | exact resolve eq122586 eq150351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122586 eq150351
  have eq150488 : (M.op x y) = (M.op x (M.op (σ y) (M.op (σ y) (M.op x y)))) ∨ y = (M.op x y) := by grind
  clear eq150485
  have eq150527 : (M.op x y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7923 eq150488
    | exact resolve eq150488 eq7923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7923 eq150488
  have eq150552 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150390 eq150527
    | exact resolve eq150527 eq150390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150390 eq150527
  have eq151080 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4016
       have i₂ := eq150552
       grind)
    | exact superpose eq150552 eq4016
    | exact resolve eq4016 eq150552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016
  have eq151099 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq130519 x
       have i₂ := eq150552
       grind)
    | exact superpose eq150552 eq130519
    | exact resolve eq130519 eq150552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130519 eq150552
  have eq151339 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq151099
  have eq151358 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq151080
  have eq151721 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151358 eq3972
    | exact resolve eq3972 eq151358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3972 eq151358
  have eq152043 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq151721
  have eq152164 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3974 eq152043
    | exact resolve eq152043 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152043
  have eq152281 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq152164
    | exact resolve eq152164 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152164
  have eq152345 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3974 eq152281
    | exact resolve eq152281 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3974 eq152281
  have eq152375 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq152345
    | exact resolve eq152345 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152345
  have eq152376 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq152375
  have eq152479 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq152376 eq27
    | exact resolve eq27 eq152376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152376
  have eq153066 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq151339
       grind)
    | exact superpose eq151339 eq40
    | exact resolve eq40 eq151339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq151339
  have eq153128 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq153066
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq153066
    | exact resolve eq153066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153066
  have eq153132 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq153128
    | exact resolve eq153128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153128
  have eq153134 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133530 eq153132
    | exact resolve eq153132 eq133530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133530 eq153132
  have eq153136 : y = (M.op x y) := by
    first
    | (have r₁ := eq153134
       have r₂ := eq152479
       grind)
    | exact resolve eq153134 eq152479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152479 eq153134
  have eq153138 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq18
    | exact resolve eq18 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq153139 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq24
    | exact resolve eq24 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq153142 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq175
    | exact resolve eq175 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq153143 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq186
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq186
    | exact resolve eq186 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq153144 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq571 X0
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq571
    | (have j0 := eq571 X0
       grind)
    | exact resolve eq571 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq153148 : (σ x) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq632
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq632
    | exact resolve eq632 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq153149 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq666
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq666
    | exact resolve eq666 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq153156 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1297 X0 X1
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq1297
    | exact resolve eq1297 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153193 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq153139 eq20
    | exact resolve eq20 eq153139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153196 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq153139 eq15
    | exact resolve eq15 eq153139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155369 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1254 (M.op X0 X1) X1 X2 X3 X1
       have i₂ := eq1163 X1 X0 X1 X0
       grind)
    | exact superpose eq1163 eq1254
    | exact resolve eq1254 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq157175 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq153142 (M.op X0 (M.op X0 X0))
       have i₂ := eq1275 X0 X0 X0
       grind)
    | exact superpose eq1275 eq153142
    | exact resolve eq153142 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157258 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq153142 eq1297
    | exact resolve eq1297 eq153142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq157336 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq103493 eq157258
    | exact resolve eq157258 eq103493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157258
  have eq157349 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq157336 X0
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq157336
    | exact resolve eq157336 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157336
  have eq158023 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq157349 eq16
    | exact resolve eq16 eq157349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160851 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1156 X0
       have i₂ := eq157175 X0
       grind)
    | (have i₁ := eq1156 (M.op x y)
       have i₂ := eq157175 (M.op x y)
       grind)
    | exact superpose eq157175 eq1156
    | exact resolve eq1156 eq157175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160872 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1275 X0 X0 X1
       have i₂ := eq157175 X0
       grind)
    | (have i₁ := eq1275 (M.op x y) (M.op x y) x
       have i₂ := eq157175 (M.op x y)
       grind)
    | exact superpose eq157175 eq1275
    | exact resolve eq1275 eq157175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq160873 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1277 X0 X0
       have i₂ := eq157175 X0
       grind)
    | (have i₁ := eq1277 (M.op x y) (M.op x y)
       have i₂ := eq157175 (M.op x y)
       grind)
    | exact superpose eq157175 eq1277
    | exact resolve eq1277 eq157175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq161027 : (σ y) = (M.op (σ x) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq630 sF3
       have i₂ := eq157175 sF3
       grind)
    | exact superpose eq157175 eq630
    | exact resolve eq630 eq157175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq157175
  have eq161181 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq161027
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq161027
    | exact resolve eq161027 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161027
  have eq161268 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq153148 eq161181
    | exact resolve eq161181 eq153148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153148 eq161181
  have eq162177 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq161268 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq161268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq161268
  have eq191565 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq153142 eq1304
    | exact resolve eq1304 eq153142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192135 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq103493 eq191565
    | exact resolve eq191565 eq103493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103493 eq191565
  have eq192354 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq157349 eq192135
    | exact resolve eq192135 eq157349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157349 eq192135
  have eq199544 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq176 eq192354
    | exact resolve eq192354 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192354
  have eq206840 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) (M.op X0 X0)) = (M.op (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) (M.op X0 X0)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq158023 eq160851
    | exact resolve eq160851 eq158023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158023 eq160851
  have eq206956 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq206840 X1 x
       have i₂ := eq155369 sF0 X1 x (M.op sF0 sF0)
       grind)
    | exact superpose eq155369 eq206840
    | exact resolve eq206840 eq155369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155369 eq206840
  have eq206998 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 X0)) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq199544 eq206956
    | exact resolve eq206956 eq199544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199544 eq206956
  have eq207201 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq206998 eq153142
    | exact resolve eq153142 eq206998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210813 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X0)))) = (M.op (M.op (M.op x y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq160872 eq1298
    | exact resolve eq1298 eq160872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq210819 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op (M.op x y) (M.op (M.op x y) X0)))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq160872 eq1254
    | exact resolve eq1254 eq160872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq210836 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op x y) (M.op (M.op x y) X3)) (M.op (M.op x y) (M.op (M.op x y) X3)))) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq160872 eq1304
    | exact resolve eq1304 eq160872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160872
  have eq211056 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op x y) X3) (M.op (M.op x y) (M.op (M.op x y) X3)))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq210836 X0 X1 X2 X3
       have i₂ := eq178 sF0 (M.op sF0 X3)
       grind)
    | exact superpose eq178 eq210836
    | exact resolve eq210836 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210836
  have eq211063 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op (M.op x y) X0)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq210819 X0 X1 X2
       have i₂ := eq178 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq178 eq210819
    | exact resolve eq210819 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210819
  have eq211064 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op (M.op x y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq153156 eq210813
    | exact resolve eq210813 eq153156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210813
  have eq211160 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (M.op x y) (M.op (M.op (M.op x y) X3) (M.op (M.op x y) X3)))) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq206998 eq211056
    | exact resolve eq211056 eq206998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211056
  have eq211166 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op x y) (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq206998 eq211063
    | exact resolve eq211063 eq206998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206998 eq211063
  have eq211210 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (M.op x y) (M.op X3 (M.op (M.op x y) X3)))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq211160 X0 X1 X2 X1
       have i₂ := eq178 sF0 X1
       grind)
    | exact superpose eq178 eq211160
    | exact resolve eq211160 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211160
  have eq211215 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) X0)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq211166 X1 X1 X2
       have i₂ := eq178 sF0 X1
       grind)
    | exact superpose eq178 eq211166
    | exact resolve eq211166 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq211166
  have eq211235 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq207201 eq211210
    | exact resolve eq211210 eq207201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211210
  have eq211240 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq207201 eq211215
    | exact resolve eq211215 eq207201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207201 eq211215
  have eq211251 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq153156 eq211235
    | exact resolve eq211235 eq153156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211235
  have eq211257 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) X0) = (M.op (M.op (M.op x y) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq211064 eq211251
    | exact resolve eq211251 eq211064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211064 eq211251
  have eq212850 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq176 eq211240
    | exact resolve eq211240 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211240
  have eq228233 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq162177 eq98
    | exact resolve eq98 eq162177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq162177
  have eq228302 : y = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq32 eq228233
    | exact resolve eq228233 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq228233
  have eq228313 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq228302
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq228302
    | exact resolve eq228302 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228302
  have eq237449 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op x y) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq176 eq211257
    | exact resolve eq211257 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq211257
  have eq242771 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op (M.op x y) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq160873 x
       have i₂ := eq237449 sF0 (M.op sF0 x) x
       grind)
    | exact superpose eq237449 eq160873
    | exact resolve eq160873 eq237449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160873 eq237449
  have eq293005 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1119 x x
       have i₂ := eq228313
       grind)
    | exact superpose eq228313 eq1119
    | (have j0 := eq1119 (M.op x y) (M.op x (M.op x y))
       grind)
    | exact resolve eq1119 eq228313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq228313
  have eq293026 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq153138 eq293005
    | exact resolve eq293005 eq153138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293005
  have eq533365 : x = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153144 x
       have i₂ := eq652
       grind)
    | exact superpose eq652 eq153144
    | (have j0 := eq153144 x
       grind)
    | exact resolve eq153144 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq153144
  have eq533696 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq533365
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq533365
    | exact resolve eq533365 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533365
  have eq533720 : (M.op x y) = (M.op x x) ∨ x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq533696
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq533696
    | exact resolve eq533696 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533696
  have eq533732 : (M.op x y) = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq293026 eq533720
    | exact resolve eq533720 eq293026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533720
  have eq533735 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq293026 eq533732
    | exact resolve eq533732 eq293026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293026 eq533732
  have eq533737 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq533735
       have r₂ := eq153149
       grind)
    | exact resolve eq533735 eq153149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153149 eq533735
  have eq533812 : x = (M.op x (M.op x (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1156 x
       have i₂ := eq533737
       grind)
    | exact superpose eq533737 eq1156
    | exact resolve eq1156 eq533737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534070 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq533737
  have eq534181 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq153138 eq533812
    | exact resolve eq533812 eq153138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533812
  have eq534229 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq153138 eq534181
    | exact resolve eq534181 eq153138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534181
  have eq534252 : x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq534229
       have r₂ := eq534070
       grind)
    | exact resolve eq534229 eq534070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534070 eq534229
  have eq534310 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq534252
       grind)
    | exact superpose eq534252 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq534252
       grind)
    | exact resolve eq13 eq534252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534524 : (σ y) = (M.op (M.op x (σ x)) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1944 x x
       have i₂ := eq534252
       grind)
    | exact superpose eq534252 eq1944
    | exact resolve eq1944 eq534252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq534603 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq534310 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534310
  have eq534621 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq534524
       have i₂ := eq212850 x sF2
       grind)
    | exact superpose eq212850 eq534524
    | exact resolve eq534524 eq212850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212850 eq534524
  have eq534714 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq534621
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq534621
    | exact resolve eq534621 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534621
  have eq535865 : x = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq534252
       have i₂ := eq534603 x
       grind)
    | exact superpose eq534603 eq534252
    | exact resolve eq534252 eq534603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534252 eq534603
  have eq536074 : x = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq535865
  have eq536941 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq613 x
       have i₂ := eq536074
       grind)
    | exact superpose eq536074 eq613
    | (have j0 := eq613 x
       grind)
    | exact resolve eq613 eq536074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq536943 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq660 x X0
       have i₂ := eq536074
       grind)
    | exact superpose eq536074 eq660
    | (have j0 := eq660 x X0
       grind)
    | exact resolve eq660 eq536074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536074
  have eq536966 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq536943 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536943
  have eq536967 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq536941
  have eq536989 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq536966 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq536966
    | (have j0 := eq536966 X0
       grind)
    | exact resolve eq536966 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536966
  have eq536990 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq536967
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq536967
    | exact resolve eq536967 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536967
  have eq537201 : (M.op (σ x) (σ x)) = (M.op (M.op x y) (M.op (M.op x y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq536990 eq140685
    | exact resolve eq140685 eq536990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140685
  have eq537214 : (σ x) = (M.op (M.op x y) (M.op (M.op x y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq536990 eq153142
    | exact resolve eq153142 eq536990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153142 eq536990
  have eq537440 : (σ x) = (M.op (M.op x y) (k (M.op x y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq536989 eq537214
    | exact resolve eq537214 eq536989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537214
  have eq537442 : x = (M.op x y) ∨ (M.op (σ x) (σ x)) = (M.op (M.op x y) (M.op (M.op x y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq537201
       have i₂ := eq153136
       grind)
    | exact superpose eq153136 eq537201
    | exact resolve eq537201 eq153136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153136 eq537201
  have eq537558 : x = (M.op x y) ∨ (σ y) = (M.op (M.op x y) (M.op (M.op x y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq534714 eq537442
    | exact resolve eq537442 eq534714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534714 eq537442
  have eq537623 : x = (M.op x y) ∨ (σ y) = (M.op (M.op x y) (k (M.op x y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq536989 eq537558
    | exact resolve eq537558 eq536989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536989 eq537558
  have eq537647 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq537440 eq537623
    | exact resolve eq537623 eq537440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537440 eq537623
  have eq537648 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq537647
  have eq538030 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq537648 eq153196
    | exact resolve eq153196 eq537648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153196 eq537648
  have eq538239 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq538030
    | exact resolve eq538030 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq538030
  have eq538240 : x = (M.op x y) := by grind
  clear eq538239
  have eq538398 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq538240
       grind)
    | exact superpose eq538240 eq22
    | exact resolve eq22 eq538240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq538642 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq153138
       have i₂ := eq538240
       grind)
    | exact superpose eq538240 eq153138
    | exact resolve eq153138 eq538240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153138 eq538240
  have eq538732 : (σ x) = (σ y) := by
    first
    | exact superpose eq538398 eq153139
    | exact resolve eq153139 eq538398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153139
  have eq538733 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq538398 eq20
    | exact resolve eq20 eq538398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538398
  have eq538847 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq538732 eq26
    | exact resolve eq26 eq538732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq539206 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq538732 eq153143
    | exact resolve eq153143 eq538732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153143
  have eq539983 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq538642 eq242771
    | exact resolve eq242771 eq538642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242771
  have eq540030 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq538642 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq538642
       grind)
    | exact resolve eq13 eq538642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540305 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq540030 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540030
  have eq540418 : ∀ X0 : G, (M.op x y) = (k (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq540305 eq539983
    | exact resolve eq539983 eq540305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539983
  have eq540521 : ∀ X0 : G, (M.op x y) = (k (k X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq540305 eq540418
    | exact resolve eq540418 eq540305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540418
  have eq540788 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq538847 eq1156
    | exact resolve eq1156 eq538847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156 eq538847
  have eq542543 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq540305 eq538642
    | exact resolve eq538642 eq540305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538642 eq540305
  have eq543848 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq542543 eq38
    | exact resolve eq38 eq542543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq543863 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq542543 eq660
    | (have j0 := eq660 (M.op x y) X0
       grind)
    | exact resolve eq660 eq542543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq542543
  have eq543886 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq543863 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543863
  have eq543902 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq543886
    | (have j0 := eq543886 X0
       grind)
    | exact resolve eq543886 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543886
  have eq543906 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq543848
    | exact resolve eq543848 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543848
  have eq543916 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq153193 eq543902
    | exact resolve eq543902 eq153193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543902
  have eq543920 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq153193 eq543906
    | exact resolve eq543906 eq153193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543906
  have eq543928 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq538732 eq543916
    | exact resolve eq543916 eq538732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543916
  have eq543932 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq538732 eq543920
    | exact resolve eq543920 eq538732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543920
  have eq555048 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq540521 eq312
    | exact resolve eq312 eq540521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq540521
  have eq555066 : ∀ X0 : G, (σ (M.op x y)) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq555048
    | (have j0 := eq555048 X0
       grind)
    | exact resolve eq555048 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq555048
  have eq555075 : ∀ X0 : G, (σ y) = (k (k X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq153193 eq555066
    | exact resolve eq555066 eq153193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153193 eq555066
  have eq555083 : ∀ X0 : G, (σ x) = (k (k X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq538732 eq555075
    | exact resolve eq555075 eq538732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538732 eq555075
  have eq556427 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq540788 eq1304
    | exact resolve eq1304 eq540788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq540788
  have eq556607 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) (σ x)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq153156 eq556427
    | exact resolve eq556427 eq153156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153156 eq556427
  have eq556650 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq539206 eq556607
    | exact resolve eq556607 eq539206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539206 eq556607
  have eq556673 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op X0 X1) (M.op (σ x) (σ x))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq543928 eq556650
    | exact resolve eq556650 eq543928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556650
  have eq556689 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op X0 X1) (k (σ x) (σ x))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq543928 eq556673
    | exact resolve eq556673 eq543928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556673
  have eq556698 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op X0 X1) (σ x)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq543932 eq556689
    | exact resolve eq556689 eq543932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543932 eq556689
  have eq556704 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (k (M.op X0 X1) (σ x)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq543928 eq556698
    | exact resolve eq556698 eq543928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543928 eq556698
  have eq556708 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq555083 eq556704
    | exact resolve eq556704 eq555083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555083 eq556704
  have eq556712 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq556708 eq27
    | exact resolve eq27 eq556708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq556708
  have eq557244 : False := by grind
  exact eq557244

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq79 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq86
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq275 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq263 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq280 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq275 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq275 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq291 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X0 X1
       have j1 := eq79 X0 (σ X1)
       grind)
    | (have r₁ := eq280 X0 X1
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq280 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq280
  have eq298 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq291
    | (have j0 := eq291 X0 X1
       grind)
    | exact resolve eq291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq299 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq305 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq299 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq299
    | exact resolve eq299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq299 x y
       grind)
    | exact superpose eq299 eq16
    | exact resolve eq16 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq400 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq305 X0 (τ X1)
       grind)
    | exact superpose eq305 eq17
    | exact resolve eq17 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq305
  have eq415 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq400 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq400
    | exact resolve eq400 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq423 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq415
    | exact resolve eq415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq435 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq316
       have i₂ := eq423 x y
       grind)
    | exact superpose eq423 eq316
    | exact resolve eq316 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq423
  have eq436 : False := by grind
  exact eq436
