import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_pyy_x_pyy_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq180 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq36
    | exact resolve eq36 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq183 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq180
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180
    | exact resolve eq180 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq192 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq203 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq192
    | exact resolve eq192 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq210 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq221 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq210
    | exact resolve eq210 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq339 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq400 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq554 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq400 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq400
    | exact resolve eq400 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq583 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq554 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq554
    | exact resolve eq554 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq730 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
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
  clear eq176
  have eq781 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq782 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k y x) = (M.op x x) := by
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
  have eq803 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) X1) X2) ∨ (M.op (M.op X0 X0) X1) = (M.op X2 X2) ∨ (M.op X0 X0) = (k X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X0 X0) X1)
       have i₂ := eq16 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq16 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op (M.op X0 X0) X1)) ∨ (M.op (M.op X0 X0) X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq805 X0 X1 X2
       grind)
    | (have r₁ := eq805 X0 X1 X2
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq805 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq847 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq808 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq885 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq847 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq847
    | (have j0 := eq847 (σ X0)
       grind)
    | exact resolve eq847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1741 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq781
       grind)
    | exact superpose eq781 eq39
    | exact resolve eq39 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1742 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1741
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1741
    | exact resolve eq1741 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741
  have eq1744 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1742
    | exact resolve eq1742 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742
  have eq8175 : ∀ X0 X1 : G, (k X1 X0) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq790 X0 X1
       have i₂ := eq808 X0
       grind)
    | exact superpose eq808 eq790
    | (have j0 := eq790 X0 X1
       have j1 := eq808 X0
       grind)
    | (have r₁ := eq790 X0 X0
       have r₂ := eq808 X0
       grind)
    | exact resolve eq790 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq8218 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ x) (σ (M.op (M.op X0 X0) X1))) ∨ (M.op (M.op X0 X0) X1) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op (M.op X0 X0) X1)
       have i₂ := eq814 X0 X1 x
       grind)
    | exact superpose eq814 eq35
    | (have j1 := eq814 X0 X1 x
       grind)
    | exact resolve eq35 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq814
  have eq16452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1744 eq782
    | exact resolve eq782 eq1744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16459 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16452
       have r₂ := eq27
       grind)
    | exact resolve eq16452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16452
  have eq16466 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16459 eq803
    | (have r₁ := eq803
       have r₂ := eq16459
       grind)
    | exact resolve eq803 eq16459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16459
  have eq16482 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq16466
  have eq16483 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq16482
  have eq16484 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1744 eq16483
    | exact resolve eq16483 eq1744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744 eq16483
  have eq16485 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16484
       have r₂ := eq27
       grind)
    | exact resolve eq16484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16484
  have eq16487 : y = (k y (τ (σ x))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16485 eq221
    | exact resolve eq221 eq16485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16485
  have eq16502 : y = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq16487
    | exact resolve eq16487 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16487
  have eq16504 : (M.op x y) = (M.op x x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16502
       have r₂ := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq16502
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16502 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16502
  have eq16506 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq802
       have i₂ := eq16504
       grind)
    | exact superpose eq16504 eq802
    | (have r₁ := eq802
       have r₂ := eq16504
       grind)
    | exact resolve eq802 eq16504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16504
  have eq16522 : x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by grind
  clear eq16506
  have eq16524 : (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16522
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16522 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16522
  have eq16554 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq16524
       grind)
    | exact superpose eq16524 eq39
    | exact resolve eq39 eq16524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16524
  have eq16556 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16554
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16554
    | exact resolve eq16554 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16554
  have eq16560 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq20 eq16556
    | exact resolve eq16556 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16556
  have eq16584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq16560 eq782
    | exact resolve eq782 eq16560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16590 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq16584
       have r₂ := eq27
       grind)
    | exact resolve eq16584 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16584
  have eq17131 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq16590 eq803
    | (have r₁ := eq803
       have r₂ := eq16590
       grind)
    | exact resolve eq803 eq16590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16590
  have eq17148 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq17131
  have eq17149 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq17148
  have eq17150 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq16560 eq17149
    | exact resolve eq17149 eq16560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16560 eq17149
  have eq17151 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq17150
       have r₂ := eq27
       grind)
    | exact resolve eq17150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17150
  have eq17153 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq17151 eq221
    | exact resolve eq221 eq17151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq17151
  have eq17169 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq29 eq17153
    | exact resolve eq17153 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17153
  have eq17170 : y = (k y x) := by grind
  clear eq17169
  have eq17177 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq781
       have i₂ := eq17170
       grind)
    | exact superpose eq17170 eq781
    | exact resolve eq781 eq17170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq17180 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq17170
       grind)
    | exact superpose eq17170 eq39
    | exact resolve eq39 eq17170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17181 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq17180
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17180
    | exact resolve eq17180 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17180
  have eq17193 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17181 eq782
    | exact resolve eq782 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq18025 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq802
       have i₂ := eq17177
       grind)
    | exact superpose eq17177 eq802
    | (have r₁ := eq802
       have r₂ := eq17177
       grind)
    | exact resolve eq802 eq17177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq17177
  have eq18050 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq18025
  have eq18051 : x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq18050
  have eq18053 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18051
       have i₂ := eq17170
       grind)
    | exact superpose eq17170 eq18051
    | exact resolve eq18051 eq17170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18051
  have eq18054 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq18053
  have eq18056 : x = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18054
       have i₂ := eq808 y
       grind)
    | exact superpose eq808 eq18054
    | (have j1 := eq808 y
       grind)
    | exact resolve eq18054 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18060 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq18054
       grind)
    | exact superpose eq18054 eq16
    | exact resolve eq16 eq18054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18065 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq730 y X1 x
       have i₂ := eq18054
       grind)
    | exact superpose eq18054 eq730
    | exact resolve eq730 eq18054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18073 : x ≠ x ∨ x = y ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq18054
       grind)
    | exact superpose eq18054 eq12
    | exact resolve eq12 eq18054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18074 : x = (k y y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq18073
  have eq18076 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18074 eq18056
    | exact resolve eq18056 eq18074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18056
  have eq18077 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18060 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18060
    | (have j0 := eq18060 y X0
       grind)
    | exact resolve eq18060 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18060
  have eq18134 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq18077 sF0
       have i₂ := eq808 sF0
       grind)
    | exact superpose eq808 eq18077
    | (have j1 := eq808 (M.op x y)
       grind)
    | exact resolve eq18077 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18148 : ∀ X0 : G, x ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18077 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq18077 (M.op x y)
       grind)
    | exact resolve eq13 eq18077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18159 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18077 eq808
    | exact resolve eq808 eq18077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18210 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18065 X0 x
       have i₂ := eq808 x
       grind)
    | exact superpose eq808 eq18065
    | (have j1 := eq808 x
       grind)
    | exact resolve eq18065 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18242 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq18065 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq18065 X0 y
       grind)
    | exact superpose eq18065 eq18
    | (have j1 := eq18065 y X0
       grind)
    | exact resolve eq18 eq18065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18065
  have eq18303 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18242 eq18210
    | (have j0 := eq18210 y
       grind)
    | exact resolve eq18210 eq18242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18210
  have eq18311 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18242 eq18303
    | exact resolve eq18303 eq18242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18303
  have eq18335 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq18242 x
       grind)
    | exact superpose eq18242 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq18242 x
       grind)
    | exact resolve eq13 eq18242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18421 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq18074
       grind)
    | exact superpose eq18074 eq40
    | exact resolve eq40 eq18074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18074
  have eq18426 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18421
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18421
    | exact resolve eq18421 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18421
  have eq18430 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18426
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18426
    | exact resolve eq18426 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18426
  have eq18483 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq18311
       grind)
    | exact superpose eq18311 eq39
    | exact resolve eq39 eq18311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18490 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18483
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18483
    | exact resolve eq18483 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18483
  have eq18494 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq18490
    | exact resolve eq18490 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18490
  have eq18590 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17193 eq803
    | (have r₁ := eq803
       have r₂ := eq17193
       grind)
    | exact resolve eq803 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq17193
  have eq18613 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18590
  have eq18614 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18613
  have eq18615 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17181 eq18614
    | exact resolve eq18614 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17181 eq18614
  have eq18616 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18615
  have eq18617 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq18616
       have i₂ := eq808 sF3
       grind)
    | exact superpose eq808 eq18616
    | (have j1 := eq808 (σ y)
       grind)
    | exact resolve eq18616 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18620 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18616 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18616
       grind)
    | exact resolve eq13 eq18616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18626 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq18616 eq730
    | exact resolve eq730 eq18616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18634 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18616 eq12
    | exact resolve eq12 eq18616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18616
  have eq18635 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18634
  have eq18637 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18635 eq18617
    | exact resolve eq18617 eq18635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18617
  have eq18762 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18626 eq26
    | (have j1 := eq18626 (σ y) X0
       grind)
    | exact resolve eq26 eq18626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18773 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op (σ x) X1) ∨ (M.op X1 X1) = (σ x) ∨ (k X1 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq18626 eq12
    | (have j0 := eq12 X1 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq18626 X0 (σ x)
       grind)
    | (have r₁ := eq12 X1 (σ x)
       have r₂ := eq18626 (σ x) X1
       grind)
    | exact resolve eq12 eq18626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18809 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (k X1 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq18773 X0 X1
       grind)
    | (have r₁ := eq18773 X0 X1
       have r₂ := eq18626 X0 X1
       grind)
    | (have r₁ := eq18773 X1 X0
       have r₂ := eq18626 X0 X1
       grind)
    | exact resolve eq18773 eq18626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18626 eq18773
  have eq18824 : ∀ X1 : G, (M.op (σ x) (σ y)) = (k X1 (σ x)) ∨ (M.op X1 X1) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq18762 eq18809
    | (have j0 := eq18809 (σ y) X1
       grind)
    | exact resolve eq18809 eq18762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18809
  have eq18859 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18762 eq808
    | exact resolve eq808 eq18762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18935 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18635 eq115
    | exact resolve eq115 eq18635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18949 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq18935
    | exact resolve eq18935 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18935
  have eq19002 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8218 x x
       have i₂ := eq18242 x
       grind)
    | exact superpose eq18242 eq8218
    | exact resolve eq8218 eq18242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19083 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq19002
    | (have j0 := eq19002 X0
       grind)
    | exact resolve eq19002 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19002
  have eq19104 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18077 eq19083
    | (have j0 := eq19083 X0
       grind)
    | exact resolve eq19083 eq18077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18077 eq19083
  have eq19118 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19104 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19104
    | (have j0 := eq19104 X0
       grind)
    | exact resolve eq19104 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19104
  have eq19533 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq18076
       grind)
    | exact superpose eq18076 eq40
    | exact resolve eq40 eq18076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18076
  have eq19539 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq19533
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19533
    | exact resolve eq19533 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19533
  have eq19543 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq19539
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19539
    | exact resolve eq19539 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19539
  have eq19547 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18242 eq19543
    | exact resolve eq19543 eq18242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18242 eq19543
  have eq20162 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18637 eq115
    | exact resolve eq115 eq18637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq18637
  have eq20178 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq20162
    | exact resolve eq20162 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20162
  have eq20411 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18134 eq174
    | exact resolve eq174 eq18134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18134
  have eq20711 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ X0)) ∨ (k X0 x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18824 eq59
    | (have j1 := eq18824 (σ X0)
       grind)
    | exact resolve eq59 eq18824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq18824
  have eq20939 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19118 eq97
    | (have j1 := eq19118 X0
       grind)
    | exact resolve eq97 eq19118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq19118
  have eq20961 : ∀ X0 : G, (M.op x y) = (k x x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq20939
    | (have j0 := eq20939 X0
       grind)
    | exact resolve eq20939 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20939
  have eq21077 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq20178 eq18762
    | exact resolve eq18762 eq20178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20178
  have eq21097 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21077
  have eq21124 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq21097
       grind)
    | exact superpose eq21097 eq40
    | exact resolve eq40 eq21097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq21097
  have eq21133 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21124
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21124
    | exact resolve eq21124 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21124
  have eq21138 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21133
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21133
    | exact resolve eq21133 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21133
  have eq21526 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq20411
  have eq21531 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21526
       have r₂ := eq18159
       grind)
    | exact resolve eq21526 eq18159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18159 eq21526
  have eq21545 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21531 eq41
    | exact resolve eq41 eq21531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21531
  have eq21552 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq21545
    | exact resolve eq21545 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21545
  have eq21556 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21552
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21552
    | exact resolve eq21552 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21552
  have eq22262 : x ≠ x ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8175 y y
       have i₂ := eq18949
       grind)
    | exact superpose eq18949 eq8175
    | (have j0 := eq8175 y y
       grind)
    | exact resolve eq8175 eq18949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18949
  have eq22305 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18430 eq8175
    | (have j0 := eq8175 (σ y) (σ y)
       grind)
    | exact resolve eq8175 eq18430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22309 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19547 eq8175
    | (have j0 := eq8175 (σ y) (σ y)
       grind)
    | exact resolve eq8175 eq19547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8175
  have eq22399 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq22309
  have eq22400 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq22399
  have eq22407 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq22305
  have eq22408 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq22407
  have eq22470 : x ≠ x ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22262
  have eq22471 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22470
  have eq22531 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22400 eq22408
    | exact resolve eq22408 eq22400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22400 eq22408
  have eq22532 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22531
  have eq22542 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18054 eq22471
    | exact resolve eq22471 eq18054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18054 eq22471
  have eq22636 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22532 eq174
    | exact resolve eq174 eq22532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22652 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22532
  have eq22674 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22636 eq18430
    | exact resolve eq18430 eq22636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18430
  have eq22678 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22636 eq19547
    | exact resolve eq19547 eq22636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19547 eq22636
  have eq22693 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq22678
  have eq22695 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq22674
  have eq22704 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22693
       have r₂ := eq22652
       grind)
    | exact resolve eq22693 eq22652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22693
  have eq22706 : x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq22695
       have r₂ := eq22652
       grind)
    | exact resolve eq22695 eq22652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22652 eq22695
  have eq22720 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq22704 eq22706
    | exact resolve eq22706 eq22704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22704 eq22706
  have eq22721 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22720
  have eq22738 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq22721 eq730
    | exact resolve eq730 eq22721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22721
  have eq22949 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22738 eq26
    | (have j1 := eq22738 (σ y) X0
       grind)
    | exact resolve eq26 eq22738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22738
  have eq23076 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22949 eq203
    | exact resolve eq203 eq22949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq23105 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22949 eq808
    | exact resolve eq808 eq22949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq22949
  have eq23380 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23105 eq18494
    | exact resolve eq18494 eq23105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18494
  have eq23397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23380
  have eq23408 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq23397
       have r₂ := eq27
       grind)
    | exact resolve eq23397 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23397
  have eq23433 : x = (k x (τ (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23408 eq23076
    | exact resolve eq23076 eq23408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23076 eq23408
  have eq23438 : x = (k x (τ (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23433
  have eq23445 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq23438
    | exact resolve eq23438 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23438
  have eq23451 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq18335 x
       grind)
    | (have r₁ := eq23445
       have r₂ := eq18335 y
       grind)
    | (have r₁ := eq23445
       have r₂ := eq18335 x
       grind)
    | exact resolve eq23445 eq18335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18335 eq23445
  have eq23471 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18311
       have i₂ := eq23451
       grind)
    | exact superpose eq23451 eq18311
    | exact resolve eq18311 eq23451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18311
  have eq23474 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20961 X0
       have i₂ := eq23451
       grind)
    | exact superpose eq23451 eq20961
    | (have j0 := eq20961 X0
       grind)
    | exact resolve eq20961 eq23451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20961
  have eq23478 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq23451
       grind)
    | exact superpose eq23451 eq39
    | exact resolve eq39 eq23451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq23451
  have eq23490 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23474 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23474
  have eq23491 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23471
  have eq23504 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23478
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23478
    | exact resolve eq23478 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23478
  have eq23517 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq23491
       grind)
    | exact superpose eq23491 eq24
    | exact resolve eq24 eq23491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23491
  have eq23579 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq23517
    | exact resolve eq23517 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23517
  have eq23739 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23504 eq23105
    | exact resolve eq23105 eq23504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23105 eq23504
  have eq23753 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23739
  have eq23770 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23753 eq27
    | exact resolve eq27 eq23753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23753
  have eq24817 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23490 eq174
    | exact resolve eq174 eq23490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq23490
  have eq24845 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq18148 (M.op x y)
       grind)
    | (have r₁ := eq24817
       have r₂ := eq18148 (M.op x y)
       grind)
    | exact resolve eq24817 eq18148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18148 eq24817
  have eq24868 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24845 eq41
    | exact resolve eq41 eq24845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq24845
  have eq24890 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq24868
    | exact resolve eq24868 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24868
  have eq24894 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21556 eq24890
    | exact resolve eq24890 eq21556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21556 eq24890
  have eq24898 : y = (M.op x y) := by
    first
    | (have r₁ := eq24894
       have r₂ := eq23770
       grind)
    | exact resolve eq24894 eq23770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23770 eq24894
  have eq24900 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24898
       grind)
    | exact superpose eq24898 eq18
    | exact resolve eq18 eq24898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24901 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq24898
       grind)
    | exact superpose eq24898 eq24
    | exact resolve eq24 eq24898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq24904 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq183
       have i₂ := eq24898
       grind)
    | exact superpose eq24898 eq183
    | exact resolve eq183 eq24898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq24931 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq17170
       have i₂ := eq24898
       grind)
    | exact superpose eq24898 eq17170
    | exact resolve eq17170 eq24898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17170
  have eq24954 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24901 eq20
    | exact resolve eq20 eq24901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25024 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq24901 eq339
    | exact resolve eq339 eq24901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq48216 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (k X0 x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq583 X0
       have i₂ := eq20711 X0
       grind)
    | exact superpose eq20711 eq583
    | (have j1 := eq20711 X0
       grind)
    | exact resolve eq583 eq20711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq20711
  have eq48276 : ∀ X0 : G, (k X0 x) = (τ (M.op (σ x) (σ y))) ∨ (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq48216
    | (have j0 := eq48216 X0
       grind)
    | exact resolve eq48216 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48216
  have eq48344 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq847 x
       have i₂ := eq48276 x
       grind)
    | exact superpose eq48276 eq847
    | (have j0 := eq847 x
       have j1 := eq48276 x
       grind)
    | (have r₁ := eq847 x
       have r₂ := eq48276 x
       grind)
    | exact resolve eq847 eq48276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48276
  have eq48492 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq847 x
       grind)
    | (have r₁ := eq48344
       have r₂ := eq847 x
       grind)
    | exact resolve eq48344 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq48344
  have eq50589 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22542 eq24904
    | exact resolve eq24904 eq22542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22542
  have eq50670 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq50589
    | exact resolve eq50589 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50589
  have eq50680 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24954 eq50670
    | exact resolve eq50670 eq24954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50670
  have eq50688 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq18620 (σ y)
       grind)
    | (have r₁ := eq50680
       have r₂ := eq18620 (σ y)
       grind)
    | exact resolve eq50680 eq18620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18620 eq50680
  have eq50695 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50688
       have i₂ := eq24898
       grind)
    | exact superpose eq24898 eq50688
    | exact resolve eq50688 eq24898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50688
  have eq50718 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50695 eq18635
    | exact resolve eq18635 eq50695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18635
  have eq50735 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50695 eq25024
    | exact resolve eq25024 eq50695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25024 eq50695
  have eq50756 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq50718
  have eq50775 : y = (k y (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq50735
    | exact resolve eq50735 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq50735
  have eq50785 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50775
       have i₂ := eq24898
       grind)
    | exact superpose eq24898 eq50775
    | exact resolve eq50775 eq24898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24898 eq50775
  have eq50855 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq50756 eq730
    | exact resolve eq730 eq50756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50944 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50785 eq885
    | (have j0 := eq885 (M.op x y)
       grind)
    | exact resolve eq885 eq50785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50785
  have eq50952 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq50944
  have eq50968 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq50952
    | exact resolve eq50952 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50952
  have eq50982 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24954 eq50968
    | exact resolve eq50968 eq24954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50968
  have eq50995 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50756 eq50982
    | exact resolve eq50982 eq50756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50756 eq50982
  have eq51354 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq24900
       have i₂ := eq50855 sF0 x
       grind)
    | (have i₁ := eq24900
       have i₂ := eq50855 X0 sF0
       grind)
    | exact superpose eq50855 eq24900
    | (have j1 := eq50855 y X0
       grind)
    | exact resolve eq24900 eq50855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50855
  have eq51783 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50995 eq18762
    | exact resolve eq18762 eq50995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50995
  have eq51818 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51783
  have eq51909 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51818 eq16
    | exact resolve eq16 eq51818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51914 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51818 eq730
    | exact resolve eq730 eq51818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq51818
  have eq52485 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24900 eq51909
    | (have j0 := eq51909 y X0
       grind)
    | exact resolve eq51909 eq24900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51909
  have eq52831 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24900
       have i₂ := eq51914 sF0 x
       grind)
    | (have i₁ := eq24900
       have i₂ := eq51914 X0 sF0
       grind)
    | exact superpose eq51914 eq24900
    | (have j1 := eq51914 y X0
       grind)
    | exact resolve eq24900 eq51914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24900 eq51914
  have eq53028 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8218 x x
       have i₂ := eq52831 x
       grind)
    | exact superpose eq52831 eq8218
    | exact resolve eq8218 eq52831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8218 eq52831
  have eq53049 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq53028
    | (have j0 := eq53028 X0
       grind)
    | exact resolve eq53028 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53028
  have eq53071 : ∀ X0 : G, (σ y) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24954 eq53049
    | (have j0 := eq53049 X0
       grind)
    | exact resolve eq53049 eq24954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53049
  have eq53081 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq52485 eq53071
    | (have j0 := eq53071 X0
       grind)
    | exact resolve eq53071 eq52485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53071
  have eq53086 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53081 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53081
    | (have j0 := eq53081 X0
       grind)
    | exact resolve eq53081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53081
  have eq53089 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18859 eq53086
    | (have j0 := eq53086 X0
       grind)
    | exact resolve eq53086 eq18859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18859 eq53086
  have eq53090 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq53089 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53089
  have eq53884 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53090 eq24904
    | exact resolve eq24904 eq53090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24904
  have eq53909 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53090 eq52485
    | exact resolve eq52485 eq53090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52485 eq53090
  have eq53935 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq53909
  have eq53957 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq53884
    | exact resolve eq53884 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53884
  have eq53966 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24954 eq53957
    | exact resolve eq53957 eq24954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53957
  have eq53971 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21138 eq53966
    | exact resolve eq53966 eq21138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21138 eq53966
  have eq53981 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53935 eq27
    | exact resolve eq27 eq53935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53935
  have eq54000 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq53981
       have r₂ := eq23579
       grind)
    | exact resolve eq53981 eq23579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23579 eq53981
  have eq54004 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54000 eq27
    | exact resolve eq27 eq54000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54061 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24954 eq54004
    | exact resolve eq54004 eq24954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54004
  have eq54387 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53971 eq27
    | exact resolve eq27 eq53971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53971
  have eq54413 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq54387
       have r₂ := eq24954
       grind)
    | exact resolve eq54387 eq24954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54387
  have eq54455 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq54413 eq48492
    | exact resolve eq48492 eq54413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48492 eq54413
  have eq54458 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq54455
  have eq54487 : x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq54458
       have r₂ := eq29
       grind)
    | exact resolve eq54458 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq54458
  have eq54824 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51354 x
       have i₂ := eq54487
       grind)
    | exact superpose eq54487 eq51354
    | exact resolve eq51354 eq54487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51354 eq54487
  have eq54851 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq54824
  have eq54866 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq54851
       have r₂ := eq54061
       grind)
    | exact resolve eq54851 eq54061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54851
  have eq54889 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq54000 eq54866
    | exact resolve eq54866 eq54000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54000 eq54866
  have eq54897 : x = (M.op x y) := by
    first
    | (have r₁ := eq54889
       have r₂ := eq54061
       grind)
    | exact resolve eq54889 eq54061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54061 eq54889
  have eq54914 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq54897
       grind)
    | exact superpose eq54897 eq22
    | exact resolve eq22 eq54897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq55014 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq24931
       have i₂ := eq54897
       grind)
    | exact superpose eq54897 eq24931
    | exact resolve eq24931 eq54897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24931 eq54897
  have eq55121 : (σ x) = (σ y) := by
    first
    | exact superpose eq54914 eq24901
    | exact resolve eq24901 eq54914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24901
  have eq55122 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq54914 eq20
    | exact resolve eq20 eq54914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54914
  have eq56546 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq55014 eq885
    | (have j0 := eq885 (M.op x y)
       grind)
    | exact resolve eq885 eq55014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq55014
  have eq56554 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq56546
  have eq56566 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq56554
    | exact resolve eq56554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq56554
  have eq56580 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24954 eq56566
    | exact resolve eq56566 eq24954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24954 eq56566
  have eq56593 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq55121 eq56580
    | exact resolve eq56580 eq55121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56580
  have eq56802 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56593 eq18762
    | exact resolve eq18762 eq56593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18762 eq56593
  have eq56842 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55121 eq56802
    | exact resolve eq56802 eq55121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55121 eq56802
  have eq56843 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56842
  have eq56875 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq56843 eq27
    | exact resolve eq27 eq56843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq56843
  have eq56920 : False := by grind
  exact eq56920

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_y_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq180 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq36
    | exact resolve eq36 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq182 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq181
    | exact resolve eq181 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq183 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq180
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180
    | exact resolve eq180 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq192 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq203 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq192
    | exact resolve eq192 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq210 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq221 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq210
    | exact resolve eq210 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq730 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
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
  have eq736 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X0 X0)
       have i₂ := eq176 X0 X1
       grind)
    | (have i₁ := eq174 (M.op X0 X0)
       have i₂ := eq176 X0 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq174
    | exact resolve eq174 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k y x) := by
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
  have eq779 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 x (M.op X0 X0)
       have i₂ := eq176 X0 x
       grind)
    | (have i₁ := eq11 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 X0 x
       grind)
    | exact superpose eq176 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq791 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq820 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq795 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq844 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq789 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq934 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq39
    | exact resolve eq39 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq934
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq934
    | exact resolve eq934 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq937 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq935
    | exact resolve eq935 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq937 eq791
    | exact resolve eq791 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq960
       have r₂ := eq27
       grind)
    | exact resolve eq960 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq972 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq967 eq221
    | exact resolve eq221 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq983 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq972
    | exact resolve eq972 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq985 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq983
       have r₂ := eq13 y x
       grind)
    | exact resolve eq983 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq987 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq790
       have i₂ := eq985
       grind)
    | exact superpose eq985 eq790
    | exact resolve eq790 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq985
       grind)
    | exact superpose eq985 eq39
    | exact resolve eq39 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq990 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq987
  have eq992 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq989
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq989
    | exact resolve eq989 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq997 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq992 eq937
    | exact resolve eq937 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq992 eq791
    | exact resolve eq791 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq992
  have eq1002 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq998
  have eq1003 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq997
  have eq1010 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq990
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq990
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq990 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq730 y X1 x
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq730
    | exact resolve eq730 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq176 y x
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq176
    | exact resolve eq176 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1020 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1018
  have eq1021 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1010
  have eq1023 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1020 eq1021
    | exact resolve eq1021 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq1021
  have eq1024 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1002
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq1002
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq1002 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1027 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1002 eq730
    | exact resolve eq730 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1002 eq176
    | exact resolve eq176 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1032 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1002 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1034 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1032
  have eq1035 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1024
  have eq1037 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1034 eq1035
    | exact resolve eq1035 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034 eq1035
  have eq1041 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq730 y X1 x
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq730
    | exact resolve eq730 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq176 y x
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq176
    | exact resolve eq176 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq1003
  have eq1102 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq1013 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq1013 X0 y
       grind)
    | exact superpose eq1013 eq18
    | (have j1 := eq1013 y X0
       grind)
    | exact resolve eq18 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1190 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11 x x
       have i₂ := eq1014 X0
       grind)
    | (have i₁ := eq11 X0 x
       have i₂ := eq1014 X0
       grind)
    | exact superpose eq1014 eq11
    | (have j0 := eq11 X0 x
       grind)
    | exact resolve eq11 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1203 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1190 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1216 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1102 eq1203
    | (have j0 := eq1203 y
       grind)
    | exact resolve eq1203 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1223 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1102 eq1216
    | (have j0 := eq1216 y
       grind)
    | exact resolve eq1216 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1224 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1223
  have eq1230 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq820 (σ X1) (σ X0)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq820
    | (have j0 := eq820 (σ X1) (σ X0)
       grind)
    | exact resolve eq820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1280 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1224
       grind)
    | exact superpose eq1224 eq39
    | exact resolve eq39 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1286 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1280
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1280
    | exact resolve eq1280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1288 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1286
    | exact resolve eq1286 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1396 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1027 eq26
    | (have j1 := eq1027 (σ y) X0
       grind)
    | exact resolve eq26 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1438 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1396 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1440 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1438 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1469 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1028 eq11
    | (have j0 := eq11 X0 (σ x)
       grind)
    | exact resolve eq11 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1482 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1469 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1495 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1396 eq1482
    | (have j0 := eq1482 (σ y)
       grind)
    | exact resolve eq1482 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq1625 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq1041 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq1041 X0 y
       grind)
    | exact superpose eq1041 eq18
    | (have j1 := eq1041 y X0
       grind)
    | exact resolve eq18 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1779 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11 x x
       have i₂ := eq1042 X0
       grind)
    | (have i₁ := eq11 X0 x
       have i₂ := eq1042 X0
       grind)
    | exact superpose eq1042 eq11
    | (have j0 := eq11 X0 x
       grind)
    | exact resolve eq11 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1802 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1779 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1828 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1625 eq1802
    | (have j0 := eq1802 y
       grind)
    | exact resolve eq1802 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq1835 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1625 eq1828
    | (have j0 := eq1828 y
       grind)
    | exact resolve eq1828 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625 eq1828
  have eq1836 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1835
  have eq1840 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1836
       grind)
    | exact superpose eq1836 eq39
    | exact resolve eq39 eq1836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1846 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1840
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1840
    | exact resolve eq1840 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq1848 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1846
    | exact resolve eq1846 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq4133 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq40
    | exact resolve eq40 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq4142 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4133
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4133
    | exact resolve eq4133 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133
  have eq4144 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4142
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4142
    | exact resolve eq4142 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4142
  have eq4146 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1102 eq4144
    | exact resolve eq4144 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq4144
  have eq4147 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4146
  have eq4249 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq4147 eq840
    | (have j0 := eq840 (σ y) X1 x
       grind)
    | exact resolve eq840 eq4147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4336 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1037 eq115
    | exact resolve eq115 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq4353 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq4336
    | exact resolve eq4336 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4336
  have eq4572 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1495 eq1288
    | (have j1 := eq1495 (σ y)
       grind)
    | exact resolve eq1288 eq1495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq1495
  have eq4583 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4572 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4572
  have eq4589 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4583 X0
       grind)
    | (have r₁ := eq4583 X0
       have r₂ := eq27
       grind)
    | exact resolve eq4583 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4583
  have eq4620 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4589 eq1396
    | (have j1 := eq4589 (σ y)
       grind)
    | exact resolve eq1396 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589
  have eq4639 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq4620
  have eq4667 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4639 eq27
    | exact resolve eq27 eq4639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4678 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  have eq5084 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq4353 eq1396
    | exact resolve eq1396 eq4353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4353
  have eq5101 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by grind
  clear eq5084
  have eq5131 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4639 eq5101
    | exact resolve eq5101 eq4639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101
  have eq5171 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq5131 eq840
    | (have j0 := eq840 (M.op x y) X1 x
       grind)
    | exact resolve eq840 eq5131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq7018 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq4249
    | (have j0 := eq4249 (σ y) X0
       grind)
    | exact resolve eq4249 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4249
  have eq7078 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4639 eq7018
    | exact resolve eq7018 eq4639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7018
  have eq7093 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7078 eq174
    | (have j1 := eq7078 X0
       grind)
    | exact resolve eq174 eq7078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7078
  have eq7113 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4147 eq7093
    | (have j0 := eq7093 X0
       grind)
    | exact resolve eq7093 eq4147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147 eq7093
  have eq7120 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7113 X0
       grind)
    | (have r₁ := eq7113 X0
       have r₂ := eq4678
       grind)
    | exact resolve eq7113 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113
  have eq7140 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7120 eq730
    | exact resolve eq730 eq7120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7120
  have eq7304 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7140 eq26
    | (have j1 := eq7140 (σ y) X0
       grind)
    | exact resolve eq26 eq7140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7140
  have eq7446 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4639 eq7304
    | exact resolve eq7304 eq4639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639 eq7304
  have eq7530 : ∀ X0 : G, (σ y) = (k X0 (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7446 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq7446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7580 : ∀ X0 : G, (σ y) = (k X0 (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7530 X0
       grind)
    | (have r₁ := eq7530 X0
       have r₂ := eq4678
       grind)
    | exact resolve eq7530 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7530
  have eq8115 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7580 eq1848
    | (have j1 := eq7580 (σ x)
       grind)
    | exact resolve eq1848 eq7580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848 eq7580
  have eq8137 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq8115
  have eq8180 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8137
       have r₂ := eq4667
       grind)
    | exact resolve eq8137 eq4667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4667 eq8137
  have eq8256 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8180 eq7446
    | exact resolve eq7446 eq8180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7446 eq8180
  have eq8267 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8256
  have eq8310 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8267
       have r₂ := eq4678
       grind)
    | exact resolve eq8267 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4678 eq8267
  have eq8317 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8310 eq27
    | exact resolve eq27 eq8310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8318 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8310 eq779
    | (have r₁ := eq779
       have r₂ := eq8310
       grind)
    | exact resolve eq779 eq8310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8319 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8318
  have eq8504 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8319 eq937
    | exact resolve eq937 eq8319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq8519 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8504
  have eq8534 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8519
       have r₂ := eq8317
       grind)
    | exact resolve eq8519 eq8317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8317 eq8519
  have eq8583 : y = (k y (τ (σ x))) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8534 eq221
    | exact resolve eq221 eq8534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq8534
  have eq8614 : y = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq8583
    | exact resolve eq8583 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8583
  have eq8616 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq8614
       have r₂ := eq13 y x
       grind)
    | exact resolve eq8614 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8614
  have eq8620 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq790
       have i₂ := eq8616
       grind)
    | exact superpose eq8616 eq790
    | exact resolve eq790 eq8616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8624 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq8616
       grind)
    | exact superpose eq8616 eq39
    | exact resolve eq39 eq8616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8616
  have eq8628 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq8620
  have eq8634 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8624
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8624
    | exact resolve eq8624 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8624
  have eq8637 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8628
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq8628
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq8628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8644 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq730 y X1 x
       have i₂ := eq8628
       grind)
    | exact superpose eq8628 eq730
    | exact resolve eq730 eq8628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8649 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq8628
       grind)
    | exact superpose eq8628 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq8628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8628
  have eq8651 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq8649
  have eq8652 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq8637
  have eq8654 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8651 eq8652
    | exact resolve eq8652 eq8651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8651 eq8652
  have eq8663 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8634 eq8319
    | exact resolve eq8319 eq8634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8319 eq8634
  have eq8671 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8663
  have eq8851 : ∀ X0 X1 : G, (k X0 x) = (M.op x X1) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x X0) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq8644 X1 X0
       have i₂ := eq11 X0 x
       grind)
    | exact superpose eq11 eq8644
    | (have j1 := eq11 X0 x
       grind)
    | exact resolve eq8644 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8885 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq8644 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq8644 X0 y
       grind)
    | exact superpose eq8644 eq18
    | (have j1 := eq8644 y X0
       grind)
    | exact resolve eq18 eq8644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8644
  have eq8996 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x X0) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq8885 eq8851
    | (have j0 := eq8851 X0 y
       grind)
    | exact resolve eq8851 eq8885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8851
  have eq9004 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq8885 eq8996
    | (have j0 := eq8996 X0
       grind)
    | exact resolve eq8996 eq8885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8996
  have eq9005 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq9004 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9004
  have eq9170 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8671 eq16
    | exact resolve eq16 eq8671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8671
  have eq9623 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq8654
       grind)
    | exact superpose eq8654 eq40
    | exact resolve eq40 eq8654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq8654
  have eq9632 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9623
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9623
    | exact resolve eq9623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9623
  have eq9634 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9632
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9632
    | exact resolve eq9632 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9632
  have eq9636 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8885 eq9634
    | exact resolve eq9634 eq8885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9634
  have eq9637 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq9636
  have eq9641 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9637 eq115
    | exact resolve eq115 eq9637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9637
  have eq9658 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq9641
    | exact resolve eq9641 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9641
  have eq9746 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq9005 x
       grind)
    | exact superpose eq9005 eq35
    | (have j1 := eq9005 x
       grind)
    | exact resolve eq35 eq9005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9005
  have eq9774 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9746
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9746
    | exact resolve eq9746 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9746
  have eq9778 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq9774
    | exact resolve eq9774 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9774
  have eq9780 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8885 eq9778
    | exact resolve eq9778 eq8885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8885 eq9778
  have eq9781 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq9780
  have eq9792 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9781 eq97
    | exact resolve eq97 eq9781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9781
  have eq9834 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq9792
    | exact resolve eq9792 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9792
  have eq9860 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq9170
    | (have j0 := eq9170 (σ y) X0
       grind)
    | exact resolve eq9170 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9170
  have eq9932 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8310 eq9860
    | exact resolve eq9860 eq8310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8310 eq9860
  have eq9953 : x = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9932 eq203
    | exact resolve eq203 eq9932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq9932
  have eq10050 : x = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq9953
    | exact resolve eq9953 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9953
  have eq10052 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9834 eq10050
    | exact resolve eq10050 eq9834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10050
  have eq10053 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq10052
  have eq10066 : (k y y) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10053 eq115
    | exact resolve eq115 eq10053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq10053
  have eq10173 : (k x x) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq10066
    | exact resolve eq10066 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq10066
  have eq10190 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9658 eq10173
    | exact resolve eq10173 eq9658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9658 eq10173
  have eq10195 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9834 eq10190
    | exact resolve eq10190 eq9834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9834 eq10190
  have eq10196 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq10195
  have eq10200 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10196
       grind)
    | exact superpose eq10196 eq18
    | exact resolve eq18 eq10196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10201 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq10196
       grind)
    | exact superpose eq10196 eq24
    | exact resolve eq24 eq10196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10208 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq790
       have i₂ := eq10196
       grind)
    | exact superpose eq10196 eq790
    | exact resolve eq790 eq10196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq10196
  have eq10224 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq10208
  have eq10225 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq10224
       have r₂ := eq13 (M.op x y) x
       grind)
    | exact resolve eq10224 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10224
  have eq10228 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq10201
    | exact resolve eq10201 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq10360 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10225 eq39
    | exact resolve eq39 eq10225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq10225
  have eq10362 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq10360
    | exact resolve eq10360 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10360
  have eq10364 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10228 eq10362
    | exact resolve eq10362 eq10228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10362
  have eq18232 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10200 eq5171
    | (have j0 := eq5171 y X0
       grind)
    | exact resolve eq5171 eq10200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5171
  have eq18263 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18232
  have eq18307 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18263 eq174
    | (have j1 := eq18263 X0
       grind)
    | exact resolve eq174 eq18263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18263
  have eq18344 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5131 eq18307
    | (have j0 := eq18307 X0
       grind)
    | exact resolve eq18307 eq5131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5131 eq18307
  have eq18345 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18344
  have eq18386 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq18345 eq730
    | exact resolve eq730 eq18345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq18345
  have eq18521 : ∀ X0 X1 : G, (k X0 x) = (M.op x X1) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x X0) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq18386 X1 X0
       have i₂ := eq11 X0 x
       grind)
    | exact superpose eq11 eq18386
    | (have j1 := eq11 X0 x
       grind)
    | exact resolve eq18386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18597 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10200
       have i₂ := eq18386 sF0 x
       grind)
    | (have i₁ := eq10200
       have i₂ := eq18386 X0 sF0
       grind)
    | exact superpose eq18386 eq10200
    | (have j1 := eq18386 y X0
       grind)
    | exact resolve eq10200 eq18386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18386
  have eq18612 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18597
  have eq18722 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x X0) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq18612 eq18521
    | (have j0 := eq18521 X0 y
       grind)
    | exact resolve eq18521 eq18612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18521
  have eq18732 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq18612 eq18722
    | (have j0 := eq18722 X0
       grind)
    | exact resolve eq18722 eq18612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18722
  have eq18733 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq18732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18732
  have eq19152 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq18733 x
       grind)
    | exact superpose eq18733 eq35
    | (have j1 := eq18733 x
       grind)
    | exact resolve eq35 eq18733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq18733
  have eq19195 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq19152
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19152
    | exact resolve eq19152 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19152
  have eq19215 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq19195
    | exact resolve eq19195 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19195
  have eq19225 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10228 eq19215
    | exact resolve eq19215 eq10228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19215
  have eq19234 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18612 eq19225
    | exact resolve eq19225 eq18612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18612 eq19225
  have eq19235 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19234
  have eq19285 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19235 eq1440
    | (have j0 := eq1440 (σ x)
       grind)
    | exact resolve eq1440 eq19235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440 eq19235
  have eq19298 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19285
  have eq19380 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19298 eq1396
    | exact resolve eq1396 eq19298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396 eq19298
  have eq19473 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19380
  have eq19517 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19473 eq27
    | exact resolve eq27 eq19473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19473
  have eq19577 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19517
       have r₂ := eq10228
       grind)
    | exact resolve eq19517 eq10228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19517
  have eq19593 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19577 eq27
    | exact resolve eq27 eq19577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19594 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19577 eq779
    | (have r₁ := eq779
       have r₂ := eq19577
       grind)
    | exact resolve eq779 eq19577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq19605 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19594
  have eq19609 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10364 eq19605
    | exact resolve eq19605 eq10364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10364 eq19605
  have eq19610 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10228 eq19593
    | exact resolve eq19593 eq10228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10228 eq19593
  have eq19611 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq19610
  have eq19638 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19609 eq736
    | exact resolve eq736 eq19609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq19609
  have eq19664 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19638 X0
       grind)
    | (have r₁ := eq19638 X0
       have r₂ := eq19611
       grind)
    | exact resolve eq19638 eq19611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19611 eq19638
  have eq19770 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19664
    | (have j0 := eq19664 (σ y)
       grind)
    | exact resolve eq19664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19664
  have eq19842 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19577 eq19770
    | exact resolve eq19770 eq19577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19577 eq19770
  have eq19864 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19842 eq141
    | exact resolve eq141 eq19842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq19842
  have eq19898 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19864
    | exact resolve eq19864 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19864
  have eq21134 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq820 x x
       have i₂ := eq19898
       grind)
    | exact superpose eq19898 eq820
    | (have j0 := eq820 x x
       grind)
    | (have r₁ := eq820 x x
       have r₂ := eq19898
       grind)
    | exact resolve eq820 eq19898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq21135 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq21134
  have eq21136 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq21135
  have eq21225 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq844 x x
       have i₂ := eq21136
       grind)
    | exact superpose eq21136 eq844
    | exact resolve eq844 eq21136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21136
  have eq21273 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19898 eq21225
    | (have j0 := eq21225 X0
       grind)
    | exact resolve eq21225 eq19898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19898 eq21225
  have eq21274 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21273
  have eq21332 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10200
       have i₂ := eq21274 sF0
       grind)
    | exact superpose eq21274 eq10200
    | (have j1 := eq21274 y
       grind)
    | exact resolve eq10200 eq21274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10200 eq21274
  have eq21348 : x = (M.op x y) := by grind
  clear eq21332
  have eq21402 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21348
       grind)
    | exact superpose eq21348 eq18
    | exact resolve eq18 eq21348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21403 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq21348
       grind)
    | exact superpose eq21348 eq22
    | exact resolve eq22 eq21348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq21410 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq778
       have i₂ := eq21348
       grind)
    | exact superpose eq21348 eq778
    | (have r₁ := eq778
       have r₂ := eq21348
       grind)
    | exact resolve eq778 eq21348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq21412 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21410
  have eq21414 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21403 eq20
    | exact resolve eq20 eq21403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21403
  have eq23407 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21412 eq36
    | exact resolve eq36 eq21412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq23414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21412 eq1230
    | (have j0 := eq1230 y (M.op x y)
       grind)
    | exact resolve eq1230 eq21412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21412
  have eq23418 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq23414
  have eq23427 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq23418
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23418
    | exact resolve eq23418 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23418
  have eq23430 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq23407
    | exact resolve eq23407 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23407
  have eq23433 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq23427
    | exact resolve eq23427 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23427
  have eq23436 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21414 eq23430
    | exact resolve eq23430 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23430
  have eq23437 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21414 eq23433
    | exact resolve eq23433 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23433
  have eq23440 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq23437
    | exact resolve eq23437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23437
  have eq23442 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq23440
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23440
    | exact resolve eq23440 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq23440
  have eq23443 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq23442
    | exact resolve eq23442 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23442
  have eq23444 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21414 eq23443
    | exact resolve eq23443 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23443
  have eq26898 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq23444 eq174
    | exact resolve eq174 eq23444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23444
  have eq26925 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23436 eq26898
    | exact resolve eq26898 eq23436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23436 eq26898
  have eq27037 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq26925
       grind)
    | exact superpose eq26925 eq16
    | exact resolve eq16 eq26925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26925
  have eq27893 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21402 eq27037
    | exact resolve eq27037 eq21402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27037
  have eq27975 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27893 eq182
    | exact resolve eq182 eq27893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq27995 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27893 eq174
    | exact resolve eq174 eq27893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq27893
  have eq28043 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq27975
    | exact resolve eq27975 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27975
  have eq28045 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21414 eq28043
    | exact resolve eq28043 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28043
  have eq28093 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27995 eq1230
    | (have j0 := eq1230 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1230 eq27995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230 eq27995
  have eq28097 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq28093
  have eq28098 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq28097
  have eq28123 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq28098
    | exact resolve eq28098 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28098
  have eq28136 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21414 eq28123
    | exact resolve eq28123 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28123
  have eq28334 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq28136 eq844
    | exact resolve eq844 eq28136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq28136
  have eq28395 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq28045 eq28334
    | (have j0 := eq28334 X0
       grind)
    | exact resolve eq28334 eq28045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28045 eq28334
  have eq28396 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq28395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28395
  have eq28444 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28396 eq26
    | (have j1 := eq28396 (σ y)
       grind)
    | exact resolve eq26 eq28396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28396
  have eq28572 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq28444
  have eq28609 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28572 eq27
    | exact resolve eq27 eq28572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28572
  have eq28625 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq28609
       have r₂ := eq21414
       grind)
    | exact resolve eq28609 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28609
  have eq28626 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28625 eq26
    | exact resolve eq26 eq28625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq28627 : y = (τ (σ x)) := by
    first
    | exact superpose eq28625 eq31
    | exact resolve eq31 eq28625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq28759 : x = y := by
    first
    | exact superpose eq29 eq28627
    | exact resolve eq28627 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28627
  have eq28773 : y = (M.op x y) := by
    first
    | (have i₁ := eq28759
       have i₂ := eq21348
       grind)
    | exact superpose eq21348 eq28759
    | exact resolve eq28759 eq21348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21348 eq28759
  have eq28778 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq183
       have i₂ := eq28773
       grind)
    | exact superpose eq28773 eq183
    | exact resolve eq183 eq28773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq28793 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq21402
       have i₂ := eq28773
       grind)
    | exact superpose eq28773 eq21402
    | exact resolve eq21402 eq28773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21402 eq28773
  have eq28811 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq28793 eq28778
    | exact resolve eq28778 eq28793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28778 eq28793
  have eq28816 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq28811
    | exact resolve eq28811 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28811
  have eq28817 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21414 eq28816
    | exact resolve eq28816 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28816
  have eq28818 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq28625 eq28817
    | exact resolve eq28817 eq28625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28625 eq28817
  have eq28946 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28626 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq28626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28626
  have eq28948 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28946
  have eq28968 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28818 eq28948
    | exact resolve eq28948 eq28818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28818 eq28948
  have eq28969 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28968
  have eq28980 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq28969 eq27
    | exact resolve eq27 eq28969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28969
  have eq28994 : False := by grind
  exact eq28994

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyy_x_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  clear eq36
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) y) X0) := by
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
  have eq179 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X2
       have i₂ := eq16 X0 X1 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq177 X0 x X2 X3
       have i₂ := eq16 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) X2) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq189 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq193 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq16 x x X0
       have i₂ := eq185 x
       grind)
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq197 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq189 eq16
    | exact resolve eq16 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq369 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ x))) = (σ (k X0 (k x x))) := by
    intro X0
    first
    | exact superpose eq97 eq38
    | exact resolve eq38 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq416 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq332 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq332
    | exact resolve eq332 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq616 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 x X2
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq180 X0 X0 X2
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq189 x
       have i₂ := eq180 sF2 x x
       grind)
    | (have i₁ := eq189 (M.op sF2 sF2)
       have i₂ := eq180 sF2 sF2 x
       grind)
    | exact superpose eq180 eq189
    | exact resolve eq189 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq633 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq197 x
       have i₂ := eq180 sF4 x x
       grind)
    | (have i₁ := eq197 (M.op sF4 sF4)
       have i₂ := eq180 sF4 sF4 x
       grind)
    | exact superpose eq180 eq197
    | exact resolve eq197 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq777 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (M.op (σ x) X0) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k X1 (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq632 eq13
    | exact resolve eq13 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ x)) = (k X1 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq633 eq13
    | exact resolve eq13 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) X0) (M.op (σ x) X0)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq632 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (k (M.op (σ x) X0) (M.op (σ x) X0))
       grind)
    | exact resolve eq11 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1027 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq633 eq11
    | (have j0 := eq11 (σ x) (k (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0))
       grind)
    | exact resolve eq11 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq1059 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq1065 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1072 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1072 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1091 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq1027 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1092 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) X0) (M.op (σ x) X0)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq1026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1096 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1010 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1110 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have j0 := eq1091 X0
       have j1 := eq813 X0 (M.op (M.op (σ x) (σ y)) X0)
       grind)
    | (have r₁ := eq1091 X0
       have r₂ := eq813 X0 x
       grind)
    | exact resolve eq1091 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq1091
  have eq1111 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq1092 X0
       have j1 := eq777 X0 (M.op (σ x) X0)
       grind)
    | (have r₁ := eq1092 X0
       have r₂ := eq777 X0 x
       grind)
    | exact resolve eq1092 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq1092
  have eq1124 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1096 X0 X1 X2
       have j1 := eq183 X0 X1 X2 X0
       grind)
    | (have r₁ := eq1096 X0 X1 X2
       have r₂ := eq183 X0 X1 X2 x
       grind)
    | exact resolve eq1096 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1096
  have eq1158 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X3) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1124 (M.op X0 X0) X2 X3
       have i₂ := eq616 X0 X1 X2
       grind)
    | (have i₁ := eq1124 (M.op X0 X0) X2 X3
       have i₂ := eq616 X0 X2 X1
       grind)
    | exact superpose eq616 eq1124
    | exact resolve eq1124 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq1159 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) X3) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1124 (M.op X0 X0) X2 X3
       have i₂ := eq180 X0 X1 X2
       grind)
    | (have i₁ := eq1124 (M.op X0 X1) (M.op X0 X1) X2
       have i₂ := eq180 X0 X1 X2
       grind)
    | exact superpose eq180 eq1124
    | exact resolve eq1124 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1169 : ∀ X0 : G, (k x x) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have i₁ := eq1124 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1124
    | (have j0 := eq1124 x y X0
       grind)
    | exact resolve eq1124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | exact superpose eq193 eq1124
    | exact resolve eq1124 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq1195 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq182 X0 X0 x
       have i₂ := eq1124 X0 X0 x
       grind)
    | exact superpose eq1124 eq182
    | exact resolve eq182 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 X2 X3 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq182 (M.op (M.op X0 x) x) X2 X3
       have i₂ := eq1124 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq1124 eq182
    | exact resolve eq182 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (M.op (M.op (σ X0) X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq1124 (σ X0) X1 X2
       grind)
    | exact superpose eq1124 eq10
    | exact resolve eq10 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213 : ∀ X0 X1 X2 : G, (τ (k X0 X0)) = (M.op (M.op (M.op (τ X0) X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416 X0 X0
       have i₂ := eq1124 (τ X0) X1 X2
       grind)
    | exact superpose eq1124 eq416
    | exact resolve eq416 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq1214 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (M.op (τ X0) X1) X1) X2)) = (k X0 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq1124 (τ X0) X1 X2
       grind)
    | exact superpose eq1124 eq34
    | exact resolve eq34 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1124
  have eq1215 : ∀ X0 X1 X2 : G, (k X0 X0) = (σ (M.op (M.op (M.op (τ X0) X1) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1214 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1214
    | exact resolve eq1214 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1233 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k x x) X0) := by
    intro X0
    first
    | (have i₁ := eq1173 X0
       have i₂ := eq1195 x
       grind)
    | exact superpose eq1195 eq1173
    | exact resolve eq1173 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1245 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) X3) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1159 X0 X1 X2 X3
       have i₂ := eq1195 X0
       grind)
    | exact superpose eq1195 eq1159
    | exact resolve eq1159 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1246 : ∀ X0 X1 X2 X3 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op (M.op (k X0 X0) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1158 X0 X1 X2 X3
       have i₂ := eq1195 X0
       grind)
    | exact superpose eq1195 eq1158
    | exact resolve eq1158 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1264 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1245 X0 X1 x x
       have i₂ := eq182 (M.op X0 X1) x x
       grind)
    | exact superpose eq182 eq1245
    | exact resolve eq1245 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq1265 : ∀ X0 X3 : G, (M.op (k X0 X0) X3) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq1246 X0 x x X3
       have i₂ := eq1201 X0 x x
       grind)
    | exact superpose eq1201 eq1246
    | exact resolve eq1246 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1271 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X0 X1
       have i₂ := eq1195 (M.op X0 X1)
       grind)
    | exact superpose eq1195 eq1264
    | exact resolve eq1264 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1310 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (M.op X0 X0) X1
       have i₂ := eq1195 (M.op X0 X0)
       grind)
    | exact superpose eq1195 eq182
    | exact resolve eq182 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1328 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq632 sF2
       have i₂ := eq1195 sF2
       grind)
    | exact superpose eq1195 eq632
    | exact resolve eq632 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq1333 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq1328
       have i₂ := eq1195 (k sF2 sF2)
       grind)
    | exact superpose eq1195 eq1328
    | exact resolve eq1328 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1343 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1310 X0 X1
       have i₂ := eq1271 X0 X0
       grind)
    | exact superpose eq1271 eq1310
    | exact resolve eq1310 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271 eq1310
  have eq1351 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq1333
       have i₂ := eq1195 sF4
       grind)
    | exact superpose eq1195 eq1333
    | exact resolve eq1333 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1355 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1343 X0 X1
       have i₂ := eq1195 X0
       grind)
    | exact superpose eq1195 eq1343
    | exact resolve eq1343 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1563 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (M.op (σ (k X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1201 (σ X1) X2 x
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq1201
    | exact resolve eq1201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2626 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (σ (M.op (M.op (M.op (τ (σ X0)) X1) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq1215 (σ X0) X1 X2
       grind)
    | exact superpose eq1215 eq10
    | exact resolve eq10 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq2657 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (σ (M.op (M.op (M.op X0 X1) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2626 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2626
    | exact resolve eq2626 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626
  have eq4916 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1059
       grind)
    | exact superpose eq1059 eq39
    | exact resolve eq39 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq4917 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4916
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4916
    | exact resolve eq4916 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4916
  have eq4919 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq4917
    | exact resolve eq4917 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4917
  have eq4921 : x = (k y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4919
       have i₂ := eq1195 y
       grind)
    | exact superpose eq1195 eq4919
    | exact resolve eq4919 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4919
  have eq4923 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq4921
       have i₂ := eq1195 x
       grind)
    | exact superpose eq1195 eq4921
    | exact resolve eq4921 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4921
  have eq5572 : ∀ X0 X1 X2 X3 : G, (σ (M.op (k X0 X0) X1)) = (M.op (M.op (M.op (σ (k X0 X0)) X2) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1211 (k X0 X0) X2 X3
       have i₂ := eq1265 X0 X1
       grind)
    | exact superpose eq1265 eq1211
    | exact resolve eq1211 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq5578 : ∀ X0 X1 X3 : G, (σ (M.op (k X0 X0) X1)) = (M.op (σ (k X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq5572 X0 X1 x X3
       have i₂ := eq1563 X0 x x
       grind)
    | exact superpose eq1563 eq5572
    | exact resolve eq5572 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572
  have eq6361 : ∀ X0 X1 : G, (σ (k (k x x) (k x x))) = (σ (M.op (M.op (k (M.op x y) (M.op x y)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2657 (k x x) X0 X1
       have i₂ := eq1233 X0
       grind)
    | exact superpose eq1233 eq2657
    | exact resolve eq2657 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2657
  have eq6648 : (σ (k (M.op x y) (M.op x y))) = (σ (k (k x x) (k x x))) := by
    first
    | (have i₁ := eq6361 x x
       have i₂ := eq1201 sF0 x x
       grind)
    | exact superpose eq1201 eq6361
    | exact resolve eq6361 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq6361
  have eq6696 : (σ (k (M.op x y) (M.op x y))) = (k (σ (k x x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq6648
       have i₂ := eq369 (k x x)
       grind)
    | exact superpose eq369 eq6648
    | exact resolve eq6648 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq6648
  have eq6723 : (σ (k (M.op x y) (M.op x y))) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq6696
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq6696
    | exact resolve eq6696 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6696
  have eq6736 : (σ (k (M.op x y) (M.op x y))) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq6723
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6723
    | exact resolve eq6723 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6723
  have eq6743 : (σ (k (M.op x y) (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1351 eq6736
    | exact resolve eq6736 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351 eq6736
  have eq6750 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq41 eq6743
    | exact resolve eq6743 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq6743
  have eq6756 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq6750
    | exact resolve eq6750 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6750
  have eq13948 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (τ (M.op (σ x) X0)) X1) X1) X2) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1111 eq1213
    | exact resolve eq1213 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq13949 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (τ (M.op (M.op (σ x) (σ y)) X0)) X1) X1) X2) = (τ (M.op (σ x) (σ x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1110 eq1213
    | exact resolve eq1213 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq1213
  have eq14245 : ∀ X0 X1 X2 : G, (τ (k (σ x) (σ x))) = (M.op (M.op (M.op (τ (M.op (M.op (σ x) (σ y)) X0)) X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13949 X0 X1 X2
       have i₂ := eq1195 sF2
       grind)
    | exact superpose eq1195 eq13949
    | exact resolve eq13949 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13949
  have eq14246 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (τ (M.op (σ x) X0)) X1) X1) X2) = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13948 X0 X1 X2
       have i₂ := eq1195 sF4
       grind)
    | exact superpose eq1195 eq13948
    | exact resolve eq13948 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13948
  have eq14337 : ∀ X0 X1 X2 : G, (k x x) = (M.op (M.op (M.op (τ (M.op (M.op (σ x) (σ y)) X0)) X1) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq97 eq14245
    | exact resolve eq14245 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq14245
  have eq14338 : ∀ X0 X1 X2 : G, (τ (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (M.op (τ (M.op (σ x) X0)) X1) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6756 eq14246
    | exact resolve eq14246 eq6756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6756 eq14246
  have eq14349 : ∀ X0 X1 X2 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op (τ (M.op (σ x) X0)) X1) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq133 eq14338
    | exact resolve eq14338 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq14338
  have eq18412 : ∀ X0 X1 X3 : G, (σ (k X0 X0)) = (M.op (σ (M.op (k X0 X0) X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1563 X0 x X3
       have i₂ := eq5578 X0 X1 x
       grind)
    | exact superpose eq5578 eq1563
    | exact resolve eq1563 eq5578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq5578
  have eq52302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq4923 eq1065
    | exact resolve eq1065 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065 eq4923
  have eq52311 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | (have r₁ := eq52302
       have r₂ := eq27
       grind)
    | exact resolve eq52302 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52302
  have eq52318 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq52311
       have i₂ := eq1195 sF3
       grind)
    | exact superpose eq1195 eq52311
    | exact resolve eq52311 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52311
  have eq52321 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq52318
       have i₂ := eq1195 sF2
       grind)
    | exact superpose eq1195 eq52318
    | exact resolve eq52318 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52318
  have eq52332 : (τ (σ x)) = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq52321 eq115
    | exact resolve eq115 eq52321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq52321
  have eq52420 : x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq52332
    | exact resolve eq52332 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52332
  have eq52421 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by grind
  clear eq52420
  have eq52464 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq52421 eq141
    | exact resolve eq141 eq52421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq52421
  have eq52516 : x = (k x x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq52464
    | exact resolve eq52464 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52464
  have eq52517 : x = (k y y) ∨ x = (k x x) := by grind
  clear eq52516
  have eq52569 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq1265 y x
       have i₂ := eq52517
       grind)
    | exact superpose eq52517 eq1265
    | exact resolve eq1265 eq52517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52571 : ∀ X0 : G, x = (M.op (k x x) X0) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq1355 y x
       have i₂ := eq52517
       grind)
    | exact superpose eq52517 eq1355
    | exact resolve eq1355 eq52517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355 eq52517
  have eq52601 : x = (k (M.op x y) (M.op x y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq52571 x
       have i₂ := eq1233 x
       grind)
    | exact superpose eq1233 eq52571
    | exact resolve eq52571 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52571
  have eq53101 : (M.op x y) = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq52569 y
       grind)
    | exact superpose eq52569 eq18
    | (have j1 := eq52569 y
       grind)
    | exact resolve eq18 eq52569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52569
  have eq53225 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq1265 x x
       have i₂ := eq53101
       grind)
    | exact superpose eq53101 eq1265
    | exact resolve eq1265 eq53101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53101
  have eq53259 : ∀ X0 : G, x = (k x x) ∨ x = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq52601 eq53225
    | exact resolve eq53225 eq52601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52601 eq53225
  have eq53313 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq39 x
       have i₂ := eq53259 X0
       grind)
    | exact superpose eq53259 eq39
    | (have j1 := eq53259 X0
       grind)
    | exact resolve eq39 eq53259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq53322 : ∀ X0 X1 : G, (k x x) = (M.op x X0) ∨ x = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1265 x x
       have i₂ := eq53259 X0
       grind)
    | exact superpose eq53259 eq1265
    | (have j1 := eq53259 X1
       grind)
    | exact resolve eq1265 eq53259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53358 : ∀ X0 X1 : G, x = (M.op (M.op x y) X1) ∨ x = (M.op x X0) := by
    intro X0 X1
    first
    | exact superpose eq53259 eq53322
    | (have j0 := eq53322 X0 X1
       have j1 := eq53259 X1
       grind)
    | exact resolve eq53322 eq53259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53259 eq53322
  have eq53365 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq53313 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53313
    | (have j0 := eq53313 X0
       grind)
    | exact resolve eq53313 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53313
  have eq53782 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq53358 eq1195
    | (have j1 := eq53358 X0 x
       grind)
    | exact resolve eq1195 eq53358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53358
  have eq53891 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq53365 eq1265
    | (have j1 := eq53365 X1
       grind)
    | exact resolve eq1265 eq53365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq53934 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq53365 eq53891
    | (have j0 := eq53891 X0 X1
       have j1 := eq53365 X1
       grind)
    | exact resolve eq53891 eq53365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53365 eq53891
  have eq54596 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53934 eq26
    | (have j1 := eq53934 (σ y) X0
       grind)
    | exact resolve eq26 eq53934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53934
  have eq54759 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq54596 eq1169
    | exact resolve eq1169 eq54596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq55733 : (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq54759 y
       grind)
    | exact superpose eq54759 eq18
    | (have j1 := eq54759 y
       grind)
    | exact resolve eq18 eq54759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54759
  have eq55872 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) X0)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18412 x X1 x
       have i₂ := eq55733
       grind)
    | exact superpose eq55733 eq18412
    | exact resolve eq18412 eq55733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18412 eq55733
  have eq55878 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) X0)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq55872
    | (have j0 := eq55872 X0 X1
       grind)
    | exact resolve eq55872 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55872
  have eq55916 : ∀ X1 : G, (σ (M.op x y)) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq54596 eq55878
    | exact resolve eq55878 eq54596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54596 eq55878
  have eq55935 : ∀ X1 : G, (σ (M.op x y)) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq55916 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55916
    | (have j0 := eq55916 X1
       grind)
    | exact resolve eq55916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55916
  have eq56229 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55935 eq26
    | (have j1 := eq55935 (σ y)
       grind)
    | exact resolve eq26 eq55935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq55935
  have eq56317 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq56229
       have r₂ := eq27
       grind)
    | exact resolve eq56229 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56229
  have eq56351 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq56317 eq27
    | exact resolve eq27 eq56317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq56365 : ∀ X0 X1 X2 : G, (k x x) = (M.op (M.op (M.op (τ (M.op (σ x) X0)) X1) X1) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq56317 eq14337
    | exact resolve eq14337 eq56317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14337 eq56317
  have eq56366 : (k x x) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq14349 eq56365
    | exact resolve eq56365 eq14349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14349 eq56365
  have eq56506 : x ≠ (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1073 x
       have i₂ := eq56366
       grind)
    | exact superpose eq56366 eq1073
    | (have j0 := eq1073 x
       grind)
    | exact resolve eq1073 eq56366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq56544 : x = (M.op x x) := by
    first
    | (have j1 := eq53782 x
       grind)
    | (have r₁ := eq56506
       have r₂ := eq53782 x
       grind)
    | exact resolve eq56506 eq53782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53782 eq56506
  have eq56556 : x = (k x x) := by
    first
    | (have i₁ := eq56544
       have i₂ := eq1195 x
       grind)
    | exact superpose eq1195 eq56544
    | exact resolve eq56544 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq56544
  have eq56580 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1233 X0
       have i₂ := eq56556
       grind)
    | exact superpose eq56556 eq1233
    | exact resolve eq1233 eq56556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq56590 : x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq56366
       have i₂ := eq56556
       grind)
    | exact superpose eq56556 eq56366
    | exact resolve eq56366 eq56556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56366 eq56556
  have eq56650 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq56590 eq56580
    | exact resolve eq56580 eq56590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56580 eq56590
  have eq57107 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq56650 y
       grind)
    | exact superpose eq56650 eq18
    | (have j1 := eq56650 y
       grind)
    | exact resolve eq18 eq56650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq56650
  have eq57256 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq57107
       grind)
    | exact superpose eq57107 eq22
    | exact resolve eq22 eq57107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq57107
  have eq57357 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq57256 eq20
    | exact resolve eq20 eq57256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq57256
  have eq57509 : False := by grind
  exact eq57509

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 X3) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X2
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq63
    | (have j0 := eq63 (σ X0) (σ X1)
       grind)
    | exact resolve eq63 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq63 X1 (τ X0)
       grind)
    | exact superpose eq63 eq18
    | (have j1 := eq63 X1 (τ X0)
       grind)
    | exact resolve eq18 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq128 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 (M.op X0 X1) X1 X2
       have i₂ := eq9 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq9 eq27
    | exact resolve eq27 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq222 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X3) X4) = (k X4 (M.op (M.op X0 X3) X3)) ∨ (M.op (M.op (M.op X0 X1) X1) X2) ≠ (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X4 (M.op (M.op X0 X3) X3)
       have i₂ := eq23 X0 X3 (M.op (M.op X0 X3) X3) X1 X2
       grind)
    | (have i₁ := eq12 X4 (M.op (M.op X0 X3) X3)
       have i₂ := eq23 X0 X1 X2 X3 (M.op (M.op X0 X3) X3)
       grind)
    | exact superpose eq23 eq12
    | (have j0 := eq12 X4 (M.op (M.op X0 X3) X3)
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq496 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq16
    | (have j1 := eq74 y x
       grind)
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq792 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq80 X0 (τ X0)
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq80 X0 (τ X0)
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq80 X0 (τ X0)
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq804 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq792 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq806 : ∀ X0 X1 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq804 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq804
    | (have j0 := eq804 X0 X1
       grind)
    | exact resolve eq804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq815 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq496
       have i₂ := eq63 y x
       grind)
    | exact superpose eq63 eq496
    | (have j1 := eq63 (σ y) (σ x)
       grind)
    | exact resolve eq496 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq818 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq815
  have eq819 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq9
    | exact resolve eq9 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq819 X0
       grind)
    | exact superpose eq819 eq16
    | (have j1 := eq819 X0
       grind)
    | exact resolve eq16 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq1183 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1168 X0
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq1168
    | exact resolve eq1168 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1184 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1183 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq6922 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq806 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq806
    | exact resolve eq806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq6971 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6922 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6922
    | (have j0 := eq6922 X0 X1
       grind)
    | exact resolve eq6922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922
  have eq6992 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq6971 X0 X1
       grind)
    | exact superpose eq6971 eq10
    | (have j1 := eq6971 X0 X1
       grind)
    | exact resolve eq10 eq6971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6971
  have eq7031 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6992 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6992
    | (have j0 := eq6992 X0 X0
       grind)
    | exact resolve eq6992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6992
  have eq7085 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7031 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7031
  have eq7086 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7085 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7085
  have eq7138 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7086 (σ X0)
       grind)
    | exact superpose eq7086 eq15
    | exact resolve eq15 eq7086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7164 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7138 X0
       have i₂ := eq7086 X0
       grind)
    | exact superpose eq7086 eq7138
    | exact resolve eq7138 eq7086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7086 eq7138
  have eq20118 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) ≠ (M.op (M.op (M.op x X1) X1) X2) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222 x X1 X2 y x
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq222
    | exact resolve eq222 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq20204 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op (M.op x y) X0) = (k X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20118 X0 x x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq20118
    | (have j0 := eq20118 X0 x x
       grind)
    | exact resolve eq20118 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20118
  have eq20272 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq20204 X0
       grind)
    | (have r₁ := eq20204 X0
       have r₂ := eq1184 y
       grind)
    | exact resolve eq20204 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq20204
  have eq2260251 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20272 X0
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq20272
    | exact resolve eq20272 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq20272
  have eq2260530 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2260251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260251
  have eq2260932 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq496
       have i₂ := eq2260530 y
       grind)
    | exact superpose eq2260530 eq496
    | exact resolve eq496 eq2260530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq2260530
  have eq2260933 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2260932
  have eq2260934 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2260933
  have eq2266902 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2260934
       grind)
    | exact superpose eq2260934 eq16
    | exact resolve eq16 eq2260934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2267004 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq2260934
       grind)
    | exact superpose eq2260934 eq9
    | exact resolve eq9 eq2260934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2267748 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2267004 X0
       have i₂ := eq2260934
       grind)
    | exact superpose eq2260934 eq2267004
    | exact resolve eq2267004 eq2260934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267004
  have eq2268117 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2267748 X0
       have i₂ := eq7164 x
       grind)
    | exact superpose eq7164 eq2267748
    | exact resolve eq2267748 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7164 eq2267748
  have eq2269435 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2268117 (σ y)
       have i₂ := eq2260934
       grind)
    | exact superpose eq2260934 eq2268117
    | exact resolve eq2268117 eq2260934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260934 eq2268117
  have eq2273258 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2269435
       grind)
    | exact superpose eq2269435 eq10
    | exact resolve eq10 eq2269435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269435
  have eq2273929 : x = (M.op x x) := by
    first
    | (have i₁ := eq2273258
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2273258
    | exact resolve eq2273258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273258
  have eq2274658 : ∀ X0 : G, x = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq128 x x x
       have i₂ := eq2273929
       grind)
    | exact superpose eq2273929 eq128
    | exact resolve eq128 eq2273929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq2275290 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2274658 X0
       have i₂ := eq2273929
       grind)
    | exact superpose eq2273929 eq2274658
    | exact resolve eq2274658 eq2273929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273929 eq2274658
  have eq2276614 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2266902
       have i₂ := eq2275290 y
       grind)
    | exact superpose eq2275290 eq2266902
    | exact resolve eq2266902 eq2275290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266902 eq2275290
  have eq2277326 : False := by grind
  exact eq2277326

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  clear eq24
  have eq54 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq99 y x
       grind)
    | exact superpose eq99 eq76
    | (have j1 := eq99 y x
       grind)
    | exact resolve eq76 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq99
    | (have j0 := eq99 (σ y) (σ x)
       grind)
    | exact resolve eq99 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq129
       have r₂ := eq27
       grind)
    | exact resolve eq129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq134 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq132
    | exact resolve eq132 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq232 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq134 eq55
    | exact resolve eq55 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq240 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq232
    | (have j0 := eq232 X0
       grind)
    | exact resolve eq232 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq241 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq134 eq240
    | exact resolve eq240 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq246 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq241 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq248 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq246
    | (have j0 := eq246 (σ y)
       grind)
    | exact resolve eq246 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq281 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq248 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq286 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq281 X0
       grind)
    | (have r₁ := eq281 X0
       have r₂ := eq134
       grind)
    | exact resolve eq281 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq281
  have eq416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq286 eq125
    | exact resolve eq125 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq286
  have eq419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq416
  have eq422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq419
    | exact resolve eq419 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq424 : x = (M.op x y) := by
    first
    | (have r₁ := eq422
       have r₂ := eq27
       grind)
    | exact resolve eq422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq426 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq424 eq20
    | exact resolve eq20 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq428 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq424 eq54
    | exact resolve eq54 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq437 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq428 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq428
    | (have j0 := eq428 X0
       grind)
    | exact resolve eq428 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq439 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq426
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq426
    | exact resolve eq426 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq440 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq424 eq437
    | exact resolve eq437 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq522 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq439 eq26
    | exact resolve eq26 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq575 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq440 y
       grind)
    | exact superpose eq440 eq18
    | (have j1 := eq440 y
       grind)
    | exact resolve eq18 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq579 : x = (M.op x x) := by
    first
    | exact superpose eq424 eq575
    | exact resolve eq575 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq575
  have eq581 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq579
       have i₂ := eq440 X0
       grind)
    | (have i₁ := eq579
       have i₂ := eq440 x
       grind)
    | exact superpose eq440 eq579
    | exact resolve eq579 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq579
  have eq599 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq581 x
       grind)
    | exact superpose eq581 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq581 x
       grind)
    | exact resolve eq13 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq607 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq604 X0
       have i₂ := eq581 X0
       grind)
    | exact superpose eq581 eq604
    | exact resolve eq604 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq604
  have eq782 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq607 (τ X0)
       grind)
    | exact superpose eq607 eq34
    | exact resolve eq34 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq607
  have eq787 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq782 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq782
    | (have j0 := eq782 X0
       grind)
    | exact resolve eq782 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq782
  have eq791 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq439 eq787
    | exact resolve eq787 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq787
  have eq804 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq791 eq99
    | (have j0 := eq99 X0 (σ (M.op x y))
       grind)
    | exact resolve eq99 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq791
  have eq806 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq806 eq522
    | exact resolve eq522 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq806
  have eq996 : False := by grind
  exact eq996

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_pyy_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
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
  clear eq36
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq192 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq191
    | exact resolve eq191 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq202 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X2
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq241 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq230
    | exact resolve eq230 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq248 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq259 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq248
    | exact resolve eq248 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq248
  have eq789 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq790 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (k X0 X1) X2) X3) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X0 X2 X3
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq792 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq1038 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 x X2
       have i₂ := eq181 X0 x X1
       grind)
    | (have i₁ := eq181 X0 X0 x
       have i₂ := eq181 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq202 x
       have i₂ := eq181 x X0 x
       grind)
    | (have i₁ := eq202 (M.op x x)
       have i₂ := eq181 x x x
       grind)
    | exact superpose eq181 eq202
    | exact resolve eq202 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1236 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq789
       grind)
    | exact superpose eq789 eq39
    | exact resolve eq39 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1237 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1236
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1236
    | exact resolve eq1236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1239 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1237
    | exact resolve eq1237 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1239 eq790
    | exact resolve eq790 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1254 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1247
       have r₂ := eq27
       grind)
    | exact resolve eq1247 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1258 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1254
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq1254
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq1254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1259 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1254 eq259
    | exact resolve eq259 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1260 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq1254 eq1038
    | exact resolve eq1038 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1266 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1254 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1269 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1266
  have eq1270 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1258
  have eq1272 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1259
    | exact resolve eq1259 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1273 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1269 eq1270
    | exact resolve eq1270 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269 eq1270
  have eq1274 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1272
       have r₂ := eq13 y x
       grind)
    | exact resolve eq1272 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1276 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq789
       have i₂ := eq1274
       grind)
    | exact superpose eq1274 eq789
    | exact resolve eq789 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq1278 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1274
       grind)
    | exact superpose eq1274 eq39
    | exact resolve eq39 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1279 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1276
  have eq1281 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1278
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1278
    | exact resolve eq1278 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1287 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1281 eq790
    | exact resolve eq790 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq1291 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1287
  have eq1299 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1279
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq1279
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq1279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1301 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1038 y X1 x
       have i₂ := eq1279
       grind)
    | exact superpose eq1279 eq1038
    | exact resolve eq1038 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1305 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 y y x
       have i₂ := eq1279
       grind)
    | exact superpose eq1279 eq181
    | exact resolve eq181 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1307 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1279
       grind)
    | exact superpose eq1279 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1310 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1307
  have eq1311 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1299
  have eq1314 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1310 eq1311
    | exact resolve eq1311 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310 eq1311
  have eq1317 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1291 eq1038
    | exact resolve eq1038 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1291 eq181
    | exact resolve eq181 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1647 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq1301 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq1301 X0 y
       grind)
    | exact superpose eq1301 eq18
    | (have j1 := eq1301 y X0
       grind)
    | exact resolve eq18 eq1301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1815 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11 x x
       have i₂ := eq1305 X0
       grind)
    | (have i₁ := eq11 X0 x
       have i₂ := eq1305 X0
       grind)
    | exact superpose eq1305 eq11
    | (have j0 := eq11 X0 x
       grind)
    | exact resolve eq11 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1840 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq1855 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1647 eq1840
    | (have j0 := eq1840 y
       grind)
    | exact resolve eq1840 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq1863 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1647 eq1855
    | (have j0 := eq1855 y
       grind)
    | exact resolve eq1855 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq1864 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1863
  have eq1869 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1864
       grind)
    | exact superpose eq1864 eq39
    | exact resolve eq39 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq1872 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1869
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1869
    | exact resolve eq1869 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1874 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1872
    | exact resolve eq1872 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872
  have eq2022 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1317 eq26
    | (have j1 := eq1317 (σ y) X0
       grind)
    | exact resolve eq26 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq2149 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1321 eq11
    | (have j0 := eq11 X0 (σ x)
       grind)
    | exact resolve eq11 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq2174 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2189 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2022 eq2174
    | (have j0 := eq2174 (σ y)
       grind)
    | exact resolve eq2174 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2803 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1281 eq824
    | (have j0 := eq824 (σ x) (σ y)
       grind)
    | exact resolve eq824 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq2816 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2803
    | exact resolve eq2803 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2803
  have eq2817 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2816
  have eq3815 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1260 eq26
    | (have j1 := eq1260 (σ y) X0
       grind)
    | exact resolve eq26 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq4559 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq842 X0 x x x
       grind)
    | exact superpose eq842 eq16
    | (have j1 := eq842 X0 x x x
       grind)
    | exact resolve eq16 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5172 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1314
       grind)
    | exact superpose eq1314 eq40
    | exact resolve eq40 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1314
  have eq5181 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5172
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5172
    | exact resolve eq5172 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5172
  have eq5183 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5181
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5181
    | exact resolve eq5181 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5181
  have eq5185 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1647 eq5183
    | exact resolve eq5183 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647 eq5183
  have eq5186 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5185
  have eq5189 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5186 eq115
    | exact resolve eq115 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5203 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq5189
    | exact resolve eq5189 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5189
  have eq6081 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2189 eq1874
    | (have j1 := eq2189 (σ y)
       grind)
    | exact resolve eq1874 eq2189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189
  have eq6092 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6081 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6081
  have eq6098 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6092 X0
       grind)
    | (have r₁ := eq6092 X0
       have r₂ := eq27
       grind)
    | exact resolve eq6092 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6092
  have eq6131 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6098 eq2022
    | (have j1 := eq6098 (σ y)
       grind)
    | exact resolve eq2022 eq6098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6098
  have eq6161 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6131
  have eq6196 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6161 eq27
    | exact resolve eq27 eq6161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6197 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ y) X0) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6161 eq180
    | exact resolve eq180 eq6161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6211 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  have eq6432 : ∀ X2 : G, (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) X2) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq6197 eq842
    | (have j0 := eq842 (σ y) x X2 x
       grind)
    | exact resolve eq842 eq6197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842 eq6197
  have eq6473 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq211 eq6432
    | exact resolve eq6432 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq6432
  have eq6494 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5186 eq6473
    | exact resolve eq6473 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6473
  have eq6503 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6161 eq6494
    | exact resolve eq6494 eq6161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6494
  have eq8792 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2022 eq4559
    | exact resolve eq4559 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq8980 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8792
  have eq9332 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6503 eq174
    | exact resolve eq174 eq6503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6503
  have eq9361 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5186 eq9332
    | exact resolve eq9332 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186 eq9332
  have eq9370 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9361
       have r₂ := eq2817
       grind)
    | exact resolve eq9361 eq2817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817 eq9361
  have eq9387 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq9370 eq1038
    | exact resolve eq1038 eq9370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9370
  have eq9473 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9387 X0 sF2
       have i₂ := eq4559 sF2
       grind)
    | exact superpose eq4559 eq9387
    | (have j1 := eq4559 (σ x)
       grind)
    | exact resolve eq9387 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9527 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9387 eq26
    | (have j1 := eq9387 (σ y) X0
       grind)
    | exact resolve eq26 eq9387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9387
  have eq9677 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6161 eq9527
    | exact resolve eq9527 eq6161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6161 eq9527
  have eq9685 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1874 eq9473
    | exact resolve eq9473 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874 eq9473
  have eq9693 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9677 eq9685
    | exact resolve eq9685 eq9677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9685
  have eq9697 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9693
       have r₂ := eq6196
       grind)
    | exact resolve eq9693 eq6196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6196 eq9693
  have eq9885 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9697 eq9677
    | exact resolve eq9677 eq9697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9677 eq9697
  have eq9901 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq9885
  have eq9944 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9901
       have r₂ := eq6211
       grind)
    | exact resolve eq9901 eq6211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6211 eq9901
  have eq9961 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq9944 eq180
    | exact resolve eq180 eq9944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11032 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq9961
    | (have j0 := eq9961 (σ y) X0
       grind)
    | exact resolve eq9961 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9961
  have eq11182 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9944 eq11032
    | exact resolve eq11032 eq9944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11032
  have eq11307 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11182 eq26
    | (have j1 := eq11182 (σ y)
       grind)
    | exact resolve eq26 eq11182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11182
  have eq11444 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9944 eq11307
    | exact resolve eq11307 eq9944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11307
  have eq11484 : x = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11444 eq241
    | exact resolve eq241 eq11444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11444
  have eq11575 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq11484
    | exact resolve eq11484 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11484
  have eq11795 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq824 x x
       have i₂ := eq11575
       grind)
    | exact superpose eq11575 eq824
    | (have j0 := eq824 x x
       grind)
    | (have r₁ := eq824 x x
       have r₂ := eq11575
       grind)
    | exact resolve eq824 eq11575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11575
  have eq11796 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11795
  have eq11797 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11796
  have eq11859 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 x x x
       have i₂ := eq11797
       grind)
    | exact superpose eq11797 eq181
    | exact resolve eq181 eq11797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11896 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11797 eq11859
    | exact resolve eq11859 eq11797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11797 eq11859
  have eq11924 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11896 y
       grind)
    | exact superpose eq11896 eq18
    | (have j1 := eq11896 y
       grind)
    | exact resolve eq18 eq11896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11896
  have eq11989 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq11924
  have eq12013 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11989
       grind)
    | exact superpose eq11989 eq18
    | exact resolve eq18 eq11989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12014 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq11989
       grind)
    | exact superpose eq11989 eq24
    | exact resolve eq24 eq11989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11989
  have eq12042 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq12014
    | exact resolve eq12014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12014
  have eq20878 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1273 eq115
    | exact resolve eq115 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1273
  have eq20910 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29 eq20878
    | exact resolve eq20878 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20878
  have eq20916 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5203 eq20910
    | exact resolve eq20910 eq5203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5203 eq20910
  have eq20919 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9944 eq20916
    | exact resolve eq20916 eq9944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20916
  have eq21167 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20919 eq3815
    | exact resolve eq3815 eq20919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3815 eq20919
  have eq21248 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq21167
  have eq21300 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9944 eq21248
    | exact resolve eq21248 eq9944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9944 eq21248
  have eq21301 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21300
  have eq21347 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21301 eq795
    | (have j0 := eq795 (M.op x y) (M.op x y) x x
       grind)
    | exact resolve eq795 eq21301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21352 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq21347 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21347
  have eq21360 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq4559 eq21352
    | (have j1 := eq4559 (M.op x y)
       grind)
    | exact resolve eq21352 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21352
  have eq21363 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq4559 eq21360
    | (have j0 := eq21360 X0 X1
       have j1 := eq4559 (M.op x y)
       grind)
    | exact resolve eq21360 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21360
  have eq21366 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21301 eq21363
    | (have j0 := eq21363 X0 X1
       grind)
    | exact resolve eq21363 eq21301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21363
  have eq21367 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq21366 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21366
  have eq21470 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1047 x
       have i₂ := eq21367 x (M.op x x)
       grind)
    | exact superpose eq21367 eq1047
    | (have j1 := eq21367 y (M.op x y)
       grind)
    | exact resolve eq1047 eq21367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21367
  have eq21547 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21301 eq21470
    | exact resolve eq21470 eq21301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21301 eq21470
  have eq21548 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21547
  have eq21597 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21548 eq795
    | (have j0 := eq795 (M.op x y) (M.op x y) x x
       grind)
    | exact resolve eq795 eq21548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq21601 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq21597 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21597
  have eq21609 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq4559 eq21601
    | (have j1 := eq4559 (M.op x y)
       grind)
    | exact resolve eq21601 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21601
  have eq21612 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21548 eq21609
    | exact resolve eq21609 eq21548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21609
  have eq21713 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1047 x
       have i₂ := eq21612 x (M.op x x)
       grind)
    | exact superpose eq21612 eq1047
    | (have j1 := eq21612 y (M.op x y)
       grind)
    | exact resolve eq1047 eq21612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq21612
  have eq21859 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21713 eq174
    | exact resolve eq174 eq21713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq21713
  have eq21911 : x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21548 eq21859
    | exact resolve eq21859 eq21548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21548 eq21859
  have eq21912 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21911
  have eq21953 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21912 eq1038
    | exact resolve eq1038 eq21912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq21912
  have eq22052 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq21953 X0 x
       have i₂ := eq4559 x
       grind)
    | exact superpose eq4559 eq21953
    | (have j1 := eq4559 x
       grind)
    | exact resolve eq21953 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq22159 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12013
       have i₂ := eq21953 sF0 x
       grind)
    | (have i₁ := eq12013
       have i₂ := eq21953 X0 sF0
       grind)
    | exact superpose eq21953 eq12013
    | (have j1 := eq21953 y X0
       grind)
    | exact resolve eq12013 eq21953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21953
  have eq22182 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq22159 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22159
  have eq22305 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22182 eq22052
    | (have j0 := eq22052 y
       grind)
    | exact resolve eq22052 eq22182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22052
  have eq22314 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22182 eq22305
    | exact resolve eq22305 eq22182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22182 eq22305
  have eq22315 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22314
  have eq22332 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq22315
       grind)
    | exact superpose eq22315 eq39
    | exact resolve eq39 eq22315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq22315
  have eq22353 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22332
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22332
    | exact resolve eq22332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22332
  have eq22357 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22353
    | exact resolve eq22353 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22353
  have eq22359 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12042 eq22357
    | exact resolve eq22357 eq12042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22357
  have eq22408 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22359 eq8980
    | exact resolve eq8980 eq22359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8980 eq22359
  have eq22427 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22408
  have eq22460 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22427 eq27
    | exact resolve eq27 eq22427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22427
  have eq22509 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22460
       have r₂ := eq12042
       grind)
    | exact resolve eq22460 eq12042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12042 eq22460
  have eq22523 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq22509 eq180
    | exact resolve eq180 eq22509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq22668 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq22523
    | (have j0 := eq22523 (σ y) X0
       grind)
    | exact resolve eq22523 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22523
  have eq22871 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22509 eq22668
    | exact resolve eq22668 eq22509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22668
  have eq23055 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22871 eq26
    | (have j1 := eq22871 (σ y)
       grind)
    | exact resolve eq26 eq22871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22871
  have eq23311 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22509 eq23055
    | exact resolve eq23055 eq22509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22509 eq23055
  have eq23443 : x = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23311 eq241
    | exact resolve eq241 eq23311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq23311
  have eq23607 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq23443
    | exact resolve eq23443 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23443
  have eq23946 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq824 x x
       have i₂ := eq23607
       grind)
    | exact superpose eq23607 eq824
    | (have j0 := eq824 x x
       grind)
    | (have r₁ := eq824 x x
       have r₂ := eq23607
       grind)
    | exact resolve eq824 eq23607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23607
  have eq23947 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq23946
  have eq23948 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq23947
  have eq24034 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 x x x
       have i₂ := eq23948
       grind)
    | exact superpose eq23948 eq181
    | exact resolve eq181 eq23948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24092 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23948 eq24034
    | exact resolve eq24034 eq23948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23948 eq24034
  have eq24171 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12013
       have i₂ := eq24092 sF0
       grind)
    | exact superpose eq24092 eq12013
    | (have j1 := eq24092 y
       grind)
    | exact resolve eq12013 eq24092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12013 eq24092
  have eq24193 : x = (M.op x y) := by grind
  clear eq24171
  have eq24262 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24193
       grind)
    | exact superpose eq24193 eq18
    | exact resolve eq18 eq24193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24263 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq24193
       grind)
    | exact superpose eq24193 eq22
    | exact resolve eq22 eq24193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq24281 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq24263 eq20
    | exact resolve eq20 eq24263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24263
  have eq24437 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq24262 eq179
    | exact resolve eq179 eq24262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq24482 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq24437 X0
       have i₂ := eq24193
       grind)
    | exact superpose eq24193 eq24437
    | exact resolve eq24437 eq24193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24193 eq24437
  have eq24528 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq24482 eq24262
    | exact resolve eq24262 eq24482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24262 eq24482
  have eq24640 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24528 eq192
    | exact resolve eq192 eq24528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq24528
  have eq24710 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq24640
    | exact resolve eq24640 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq24640
  have eq24722 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq24281 eq24710
    | exact resolve eq24710 eq24281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24710
  have eq24921 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24722 eq824
    | (have j0 := eq824 (σ x) (σ x)
       grind)
    | (have r₁ := eq824 (σ x) (σ x)
       have r₂ := eq24722
       grind)
    | exact resolve eq824 eq24722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq24722
  have eq24922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq24921
  have eq24923 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq24922
  have eq25039 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq24923 eq181
    | exact resolve eq181 eq24923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq25056 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq24923 eq25039
    | exact resolve eq25039 eq24923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24923 eq25039
  have eq25111 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25056 eq26
    | (have j1 := eq25056 (σ y)
       grind)
    | exact resolve eq26 eq25056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq25056
  have eq25239 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq25111 eq27
    | exact resolve eq27 eq25111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25111
  have eq25251 : False := by grind
  exact eq25251

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
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
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
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
  clear eq36
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
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
  clear eq45
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
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq181 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ X4 ∨ (M.op X0 X4) = (k X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X4 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X4 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X0 X1) X2) X3) X0
       have r₂ := eq16 X0 X1 X2 X3
       grind)
    | (have r₁ := eq13 (M.op X0 X0) (M.op (M.op X0 X1) X2)
       have r₂ := eq16 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq423 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq339 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq339
    | exact resolve eq339 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq553 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (k (τ X0) (k y y)) := by
    intro X0
    first
    | exact superpose eq116 eq423
    | exact resolve eq423 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq624 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (k X0 X1) X2) X3) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X0 X2 X3
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X1 (M.op (M.op (k X0 X1) X2) X3)
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
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
  have eq654 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq664 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq40
    | exact resolve eq40 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq664
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq664
    | exact resolve eq664 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq667 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq665
    | exact resolve eq665 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq667 eq654
    | exact resolve eq654 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq677
       have r₂ := eq27
       grind)
    | exact resolve eq677 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq688 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq684
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq684
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq684 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq684 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq693 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq691 eq688
    | exact resolve eq688 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq704 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) X1) (M.op (σ y) X1)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq684 eq181
    | exact resolve eq181 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq684 eq181
    | exact resolve eq181 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 x X1
       have i₂ := eq181 X0 x X2
       grind)
    | (have i₁ := eq181 X0 X0 x
       have i₂ := eq181 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : ∀ X0 : G, (k (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq741 eq187
    | exact resolve eq187 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq741 eq26
    | (have j1 := eq741 (σ y)
       grind)
    | exact resolve eq26 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (σ x) X0) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq741 eq884
    | exact resolve eq884 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq906 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) X0) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq889 eq900
    | exact resolve eq900 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq910 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq889 eq741
    | exact resolve eq741 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq889
  have eq923 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq910 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1144 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq691 eq116
    | exact resolve eq116 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq1150 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq1144
    | exact resolve eq1144 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1809 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq693 eq116
    | exact resolve eq116 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq1816 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq1809
    | exact resolve eq1809 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq1839 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq1816 eq923
    | exact resolve eq923 eq1816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1849 : x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1839
  have eq2138 : ∀ X0 X1 : G, (k (M.op (σ x) X0) (M.op (σ y) X1)) = (M.op (M.op (σ y) X1) (M.op (σ x) X0)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq716 eq187
    | exact resolve eq187 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq2172 : ∀ X1 : G, (k (M.op (σ x) (σ y)) (M.op (σ y) X1)) = (M.op (M.op (σ y) X1) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    intro X1
    first
    | exact superpose eq923 eq2138
    | (have j0 := eq2138 (σ y) X1
       grind)
    | exact resolve eq2138 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq2138
  have eq2420 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq2172 eq16
    | exact resolve eq16 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2433 : ∀ X0 X1 : G, (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ y) X0)) X1) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq684 eq2420
    | exact resolve eq2420 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420
  have eq2468 : ∀ X0 : G, (σ x) = (k (M.op (k (M.op (σ x) (σ y)) (M.op (σ y) X0)) (k (M.op (σ x) (σ y)) (M.op (σ y) X0))) (k (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2433 eq187
    | exact resolve eq187 eq2433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2471 : ∀ X0 : G, (σ x) = (k (σ x) (k (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2433 eq2468
    | exact resolve eq2468 eq2433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433 eq2468
  have eq2526 : ∀ X0 : G, (τ (σ x)) = (k x (τ (k (M.op (σ x) (σ y)) (M.op (σ y) X0)))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2471 eq91
    | exact resolve eq91 eq2471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq2471
  have eq2529 : ∀ X0 : G, x = (k x (τ (k (M.op (σ x) (σ y)) (M.op (σ y) X0)))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq30 eq2526
    | exact resolve eq2526 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526
  have eq4047 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq684 eq704
    | exact resolve eq704 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq4100 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq187 (M.op X0 X0)
       have i₂ := eq704 X0
       grind)
    | exact superpose eq704 eq187
    | (have j1 := eq704 X0
       grind)
    | exact resolve eq187 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq4102 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) (M.op X0 X0) X2 x
       have i₂ := eq704 X0
       grind)
    | exact superpose eq704 eq16
    | (have j1 := eq704 X0
       grind)
    | exact resolve eq16 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq4115 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq4102 eq4100
    | (have j0 := eq4100 X0
       have j1 := eq4102 X0 x x
       grind)
    | exact resolve eq4100 eq4102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100 eq4102
  have eq4116 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115
  have eq4134 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq667 eq4047
    | exact resolve eq4047 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq4228 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4134 eq906
    | exact resolve eq906 eq4134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq4134
  have eq4248 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4228
  have eq4283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq667 eq4248
    | exact resolve eq4248 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq4248
  have eq4295 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq4283
       have r₂ := eq27
       grind)
    | exact resolve eq4283 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq4306 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op y X1) (M.op y X1)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq181 y X1 X0
       have i₂ := eq4295
       grind)
    | exact superpose eq4295 eq181
    | exact resolve eq181 eq4295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4309 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y y x x
       have i₂ := eq4295
       grind)
    | exact superpose eq4295 eq16
    | exact resolve eq16 eq4295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4313 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq181 y y x
       have i₂ := eq4295
       grind)
    | exact superpose eq4295 eq181
    | exact resolve eq181 eq4295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq4295
  have eq4354 : ∀ X2 X3 : G, (M.op x X2) ≠ X3 ∨ (M.op x X3) = (k X3 x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2 X3
    first
    | (have i₁ := eq185 x x x X2 X3
       have i₂ := eq4309 x x
       grind)
    | exact superpose eq4309 eq185
    | (have j0 := eq185 x x X2 X3 X3
       grind)
    | exact resolve eq185 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4531 : ∀ X0 X1 X2 : G, (k x x) = (M.op (M.op (M.op x X0) X1) X2) ∨ x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq636 x x X2 x
       have i₂ := eq4313 X0
       grind)
    | (have i₁ := eq636 x X0 X2 x
       have i₂ := eq4313 X0
       grind)
    | exact superpose eq4313 eq636
    | (have j0 := eq636 x X0 X1 X2
       grind)
    | exact resolve eq636 eq4313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq4532 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4313 y
       grind)
    | exact superpose eq4313 eq18
    | (have j1 := eq4313 y
       grind)
    | exact resolve eq18 eq4313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4313
  have eq4546 : ∀ X0 : G, (k x x) = (M.op x x) ∨ x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4531 X0 x x
       have i₂ := eq16 x X0 x x
       grind)
    | exact superpose eq16 eq4531
    | (have j0 := eq4531 X0 x x
       grind)
    | exact resolve eq4531 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4531
  have eq4555 : (k x x) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq4354 x x
       grind)
    | (have r₁ := eq4546 x
       have r₂ := eq4354 x (k x x)
       grind)
    | (have r₁ := eq4546 x
       have r₂ := eq4354 x x
       grind)
    | exact resolve eq4546 eq4354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4354 eq4546
  have eq4559 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4532 eq4555
    | exact resolve eq4555 eq4532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4532 eq4555
  have eq4605 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4559
       grind)
    | exact superpose eq4559 eq40
    | exact resolve eq40 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq4610 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq4605
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4605
    | exact resolve eq4605 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4605
  have eq4612 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq4610
    | exact resolve eq4610 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610
  have eq6851 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq624 X0 X1 X2 X3
       grind)
    | exact superpose eq624 eq16
    | (have j1 := eq624 X0 X1 X2 X3
       grind)
    | exact resolve eq16 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq6925 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6851 X0 x x x
       have j1 := eq185 X0 x x x X0
       grind)
    | (have r₁ := eq6851 (M.op (M.op X0 x) x) x x x
       have r₂ := eq185 X0 x x (M.op (M.op X0 x) x) (k (M.op (M.op X0 x) x) (M.op (M.op X0 x) x))
       grind)
    | (have r₁ := eq6851 x x x x
       have r₂ := eq185 x x x x x
       grind)
    | (have r₁ := eq6851 (M.op (M.op (M.op X0 x) x) x) x x x
       have r₂ := eq185 X0 x x x (M.op (M.op (M.op (M.op (M.op (M.op X0 x) x) x) x) x) x)
       grind)
    | exact resolve eq6851 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq6851
  have eq8118 : ∀ X0 X2 : G, (M.op y y) = (M.op (M.op x X0) X2) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X2
    first
    | (have i₁ := eq16 y x (M.op y x) X2
       have i₂ := eq4306 X0 x
       grind)
    | exact superpose eq4306 eq16
    | exact resolve eq16 eq4306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4306
  have eq8195 : ∀ X0 X2 : G, (k y y) = (M.op (M.op x X0) X2) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X2
    first
    | (have i₁ := eq8118 X0 X2
       have i₂ := eq6925 y
       grind)
    | exact superpose eq6925 eq8118
    | exact resolve eq8118 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8118
  have eq8250 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4309 eq8195
    | exact resolve eq8195 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309 eq8195
  have eq8344 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq8250
       grind)
    | exact superpose eq8250 eq41
    | exact resolve eq41 eq8250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq8250
  have eq8350 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq8344
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8344
    | exact resolve eq8344 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8344
  have eq8354 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq8350
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8350
    | exact resolve eq8350 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8350
  have eq8363 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq8354 eq637
    | (have j0 := eq637 (σ y) (M.op (M.op (σ x) X0) X1) x x
       grind)
    | exact resolve eq637 eq8354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8364 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq8363 X0 X1
       have i₂ := eq6925 sF3
       grind)
    | exact superpose eq6925 eq8363
    | exact resolve eq8363 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8363
  have eq8370 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq8364 X0 X1
       have i₂ := eq6925 sF3
       grind)
    | exact superpose eq6925 eq8364
    | (have j0 := eq8364 X0 X1
       grind)
    | exact resolve eq8364 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8364
  have eq8375 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq8354 eq8370
    | (have j0 := eq8370 X0 X1
       grind)
    | exact resolve eq8370 eq8354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8370
  have eq8376 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq8354 eq8375
    | exact resolve eq8375 eq8354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8354 eq8375
  have eq9929 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X2) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f9929_15 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x y)) := by
      intro X0 X1
      grind
    have f9929_23 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
      intro X0 X1 X2 X3
      grind
    have f9929_24 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) X2) := by grind
    have f9929_25 : (σ x) ≠ (σ y) := by grind
    have f9929_26 : (σ y) ≠ (σ (M.op x y)) := by grind
    have f9929_29 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (σ (M.op x y)) := by
      intro X0 X1
      first
      | (have j0 := f9929_15 X0 X1
         grind)
      | (have r₁ := f9929_15 X0 X1
         have r₂ := f9929_25
         grind)
      | exact resolve f9929_15 f9929_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9929_30 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) := by
      intro X0 X1
      first
      | (have j0 := f9929_29 X0 X1
         grind)
      | (have r₁ := f9929_29 X0 X1
         have r₂ := f9929_26
         grind)
      | exact resolve f9929_29 f9929_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9929_43 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X2) := by
      intro X2
      first
      | (have i₁ := f9929_23 (σ x) x x X2
         have i₂ := f9929_30 x x
         grind)
      | exact superpose f9929_30 f9929_23
      | exact resolve f9929_23 f9929_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9929_67 : ∀ X0 : G, (M.op (σ x) X0) ≠ (M.op (σ x) X2) := by
      intro X0
      first
      | (have i₁ := f9929_24
         have i₂ := f9929_43 X0
         grind)
      | (have i₁ := f9929_24
         have i₂ := f9929_43 (σ x)
         grind)
      | exact superpose f9929_43 f9929_24
      | (have r₁ := f9929_24
         have r₂ := f9929_43 X2
         grind)
      | exact resolve f9929_24 f9929_43
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f9929_178 : False := by grind
    exact f9929_178
  clear eq8376
  have eq9997 : ∀ X2 : G, (k (σ x) (σ x)) = (M.op (σ x) X2) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | (have i₁ := eq9929 X2
       have i₂ := eq6925 sF2
       grind)
    | exact superpose eq6925 eq9929
    | exact resolve eq9929 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9929
  have eq10030 : ∀ X2 : G, (σ (M.op x y)) = (M.op (σ x) X2) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X2
    first
    | exact superpose eq4612 eq9997
    | exact resolve eq9997 eq4612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9997
  have eq10222 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10030 eq26
    | (have j1 := eq10030 (σ y)
       grind)
    | exact resolve eq26 eq10030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10030
  have eq10268 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq10222
       have r₂ := eq27
       grind)
    | exact resolve eq10222 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10222
  have eq10290 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10268 eq26
    | exact resolve eq26 eq10268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10268
  have eq10358 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq10290
       have i₂ := eq6925 sF2
       grind)
    | exact superpose eq6925 eq10290
    | exact resolve eq10290 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10290
  have eq10366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4612 eq10358
    | exact resolve eq10358 eq4612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4612 eq10358
  have eq10373 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq10366
       have r₂ := eq27
       grind)
    | exact resolve eq10366 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10366
  have eq10374 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq10373 eq29
    | exact resolve eq29 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10379 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq10373 eq125
    | exact resolve eq125 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10382 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ y))) := by
    first
    | exact superpose eq10373 eq134
    | exact resolve eq134 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10389 : (k (M.op x y) (M.op x y)) = (k y (τ (σ y))) := by
    first
    | exact superpose eq108 eq10382
    | exact resolve eq10382 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq10382
  have eq10397 : (k y y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32 eq10389
    | exact resolve eq10389 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10389
  have eq10796 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq125 (M.op sF1 sF1)
       have i₂ := eq4116 sF1
       grind)
    | exact superpose eq4116 eq125
    | exact resolve eq125 eq4116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq4116
  have eq10801 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (k (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq10796
       have i₂ := eq6925 sF1
       grind)
    | exact superpose eq6925 eq10796
    | exact resolve eq10796 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10796
  have eq10842 : (τ (σ (M.op x y))) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq134 eq10801
    | exact resolve eq10801 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq10801
  have eq10871 : (M.op x y) = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq29 eq10842
    | exact resolve eq10842 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10842
  have eq10902 : y = (M.op x y) := by
    first
    | exact superpose eq10374 eq32
    | exact resolve eq32 eq10374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq10906 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq10374 eq39
    | exact resolve eq39 eq10374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq10908 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10374 eq14
    | exact resolve eq14 eq10374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10909 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10902
       grind)
    | exact superpose eq10902 eq18
    | exact resolve eq18 eq10902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq10913 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq646
       have i₂ := eq10902
       grind)
    | exact superpose eq10902 eq646
    | exact resolve eq646 eq10902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq10914 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1150
       have i₂ := eq10902
       grind)
    | exact superpose eq10902 eq1150
    | exact resolve eq1150 eq10902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq10916 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1849
       have i₂ := eq10902
       grind)
    | exact superpose eq10902 eq1849
    | exact resolve eq1849 eq10902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849 eq10902
  have eq10946 : x = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10916
       have i₂ := eq6925 sF0
       grind)
    | exact superpose eq6925 eq10916
    | exact resolve eq10916 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10916
  have eq10947 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10946
  have eq10949 : x = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10914
       have i₂ := eq6925 sF0
       grind)
    | exact superpose eq6925 eq10914
    | exact resolve eq10914 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10914
  have eq10950 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq10949
  have eq10951 : (M.op x y) = (k (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq10913
       have i₂ := eq6925 sF0
       grind)
    | exact superpose eq6925 eq10913
    | exact resolve eq10913 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10913
  have eq11427 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10947 eq38
    | exact resolve eq38 eq10947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11438 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11427
    | exact resolve eq11427 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11427
  have eq11444 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10373 eq11438
    | exact resolve eq11438 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11438
  have eq11447 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11444
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11444
    | exact resolve eq11444 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11444
  have eq11451 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10950 eq38
    | exact resolve eq38 eq10950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq10950
  have eq11462 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq11451
    | exact resolve eq11451 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11451
  have eq11468 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10373 eq11462
    | exact resolve eq11462 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11462
  have eq11471 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11468
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11468
    | exact resolve eq11468 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11468
  have eq11513 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq11471 eq637
    | (have j0 := eq637 (σ y) (M.op (M.op (σ x) X0) X1) x x
       grind)
    | exact resolve eq637 eq11471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11514 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq11513 X0 X1
       have i₂ := eq6925 sF3
       grind)
    | exact superpose eq6925 eq11513
    | exact resolve eq11513 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11513
  have eq11520 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq11514 X0 X1
       have i₂ := eq6925 sF3
       grind)
    | exact superpose eq6925 eq11514
    | (have j0 := eq11514 X0 X1
       grind)
    | exact resolve eq11514 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11514
  have eq11527 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq11471 eq11520
    | (have j0 := eq11520 X0 X1
       grind)
    | exact resolve eq11520 eq11471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11520
  have eq11528 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq11527 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11527
  have eq11533 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq11471 eq11528
    | exact resolve eq11528 eq11471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11471 eq11528
  have eq11592 : (k (M.op x y) (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq654 eq10379
    | exact resolve eq10379 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq10379
  have eq11667 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq11592
    | exact resolve eq11592 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11592
  have eq11693 : (σ x) = (k (σ y) (σ y)) ∨ (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11667
       have i₂ := eq6925 sF3
       grind)
    | exact superpose eq6925 eq11667
    | exact resolve eq11667 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11667
  have eq11709 : (σ x) = (k (σ y) (σ y)) ∨ (τ (σ x)) = (k (M.op x y) x) := by
    first
    | exact superpose eq11447 eq11693
    | exact resolve eq11693 eq11447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11447 eq11693
  have eq11717 : (σ x) = (k (σ y) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq11709
    | exact resolve eq11709 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11709
  have eq12232 : (τ (σ x)) = (k y y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq11717 eq116
    | exact resolve eq116 eq11717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq11717
  have eq12250 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq12232
       have i₂ := eq10397
       grind)
    | exact superpose eq10397 eq12232
    | exact resolve eq12232 eq10397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12232
  have eq12259 : x = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq12250
    | exact resolve eq12250 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250
  have eq12266 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10951 eq12259
    | exact resolve eq12259 eq10951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10951 eq12259
  have eq12282 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12266 eq637
    | (have j0 := eq637 (M.op x y) (M.op (M.op x X0) X1) x x
       grind)
    | exact resolve eq637 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq12284 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq12282 X0 X1
       have i₂ := eq6925 sF0
       grind)
    | exact superpose eq6925 eq12282
    | exact resolve eq12282 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12282
  have eq12292 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq12284 X0 X1
       have i₂ := eq6925 sF0
       grind)
    | exact superpose eq6925 eq12284
    | (have j0 := eq12284 X0 X1
       grind)
    | exact resolve eq12284 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12284
  have eq12300 : ∀ X0 X1 : G, x = (M.op x y) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12266 eq12292
    | (have j0 := eq12292 X0 X1
       grind)
    | exact resolve eq12292 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12292
  have eq12301 : ∀ X0 X1 : G, x = (M.op x y) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq12300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12300
  have eq12306 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq12266 eq12301
    | exact resolve eq12301 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12301
  have eq12661 : x = (k x (τ (k (M.op (σ x) (σ y)) (k (σ y) (σ y))))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2529 sF3
       have i₂ := eq6925 sF3
       grind)
    | exact superpose eq6925 eq2529
    | exact resolve eq2529 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529
  have eq12676 : x = (k x (k (τ (M.op (σ x) (σ y))) (k y y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq553 eq12661
    | exact resolve eq12661 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq12661
  have eq12787 : x = (k x (k (τ (M.op (σ x) (σ y))) (k (M.op x y) (M.op x y)))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12676
       have i₂ := eq10397
       grind)
    | exact superpose eq10397 eq12676
    | exact resolve eq12676 eq10397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12676
  have eq12857 : x = (k y y) ∨ x = (k x (k (τ (M.op (σ x) (σ y))) (k (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq12787
       have i₂ := eq6925 y
       grind)
    | exact superpose eq6925 eq12787
    | exact resolve eq12787 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12787
  have eq12906 : x = (k (M.op x y) (M.op x y)) ∨ x = (k x (k (τ (M.op (σ x) (σ y))) (k (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq12857
       have i₂ := eq10397
       grind)
    | exact superpose eq10397 eq12857
    | exact resolve eq12857 eq10397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10397 eq12857
  have eq12940 : x = (k (M.op x y) (M.op x y)) ∨ x = (k x (k (τ (σ x)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq10947 eq12906
    | exact resolve eq12906 eq10947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10947 eq12906
  have eq12970 : x = (k x (k x (k (M.op x y) (M.op x y)))) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq12940
    | exact resolve eq12940 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12940
  have eq12991 : (M.op x y) = (k (M.op x y) (k (M.op x y) (k (M.op x y) (M.op x y)))) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12266 eq12970
    | exact resolve eq12970 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12970
  have eq13004 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10871 eq12991
    | exact resolve eq12991 eq10871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10871 eq12991
  have eq13697 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq13004
  have eq13700 : x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq13697
       have r₂ := eq12266
       grind)
    | exact resolve eq13697 eq12266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12266 eq13697
  have eq13714 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13700 eq10906
    | exact resolve eq10906 eq13700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10906 eq13700
  have eq13725 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq13714
    | exact resolve eq13714 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13714
  have eq13733 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq10373 eq13725
    | exact resolve eq13725 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13725
  have eq13738 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13733
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13733
    | exact resolve eq13733 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13733
  have eq13848 : ∀ X1 X2 : G, (M.op x X1) = (M.op x X2) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq742 (M.op x x) X1 X2
       have i₂ := eq12306 x (M.op x x)
       grind)
    | exact superpose eq12306 eq742
    | exact resolve eq742 eq12306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12306
  have eq14233 : ∀ X1 X2 : G, (M.op (σ x) X1) = (M.op (σ x) X2) ∨ (σ x) = (σ y) := by
    intro X1 X2
    first
    | exact superpose eq11533 eq742
    | exact resolve eq742 eq11533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq11533
  have eq14604 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10909
       have i₂ := eq13848 sF0 x
       grind)
    | (have i₁ := eq10909
       have i₂ := eq13848 x sF0
       grind)
    | exact superpose eq13848 eq10909
    | (have j1 := eq13848 y X0
       grind)
    | exact resolve eq10909 eq13848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10909 eq13848
  have eq14738 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6925 x
       have i₂ := eq14604 x
       grind)
    | exact superpose eq14604 eq6925
    | exact resolve eq6925 eq14604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14604
  have eq14800 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq14738
       grind)
    | exact superpose eq14738 eq40
    | exact resolve eq40 eq14738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq14738
  have eq14807 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14800
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14800
    | exact resolve eq14800 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14800
  have eq14816 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq14807
    | exact resolve eq14807 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807
  have eq14824 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10373 eq14816
    | exact resolve eq14816 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14816
  have eq15176 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq14233 eq26
    | (have j1 := eq14233 (σ y) X0
       grind)
    | exact resolve eq26 eq14233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14233
  have eq15350 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15176 eq6925
    | exact resolve eq6925 eq15176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15176
  have eq15420 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15350 eq14824
    | exact resolve eq14824 eq15350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14824 eq15350
  have eq15469 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15420 eq27
    | exact resolve eq27 eq15420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15420
  have eq15558 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15469
       have r₂ := eq10373
       grind)
    | exact resolve eq15469 eq10373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10373 eq15469
  have eq15668 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15558 eq10374
    | exact resolve eq10374 eq15558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10374 eq15558
  have eq15687 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq15668
    | exact resolve eq15668 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15668
  have eq15688 : x = (M.op x y) := by grind
  clear eq15687
  have eq15729 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq15688
       grind)
    | exact superpose eq15688 eq22
    | exact resolve eq22 eq15688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15688
  have eq15858 : (σ x) = (σ y) := by
    first
    | exact superpose eq15729 eq10908
    | exact resolve eq10908 eq15729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10908
  have eq15859 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15729 eq20
    | exact resolve eq20 eq15729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15729
  have eq15895 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15858 eq26
    | exact resolve eq26 eq15858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq15954 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq15858 eq13738
    | exact resolve eq13738 eq15858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13738 eq15858
  have eq15987 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15895
       have i₂ := eq6925 sF2
       grind)
    | exact superpose eq6925 eq15895
    | exact resolve eq15895 eq6925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6925 eq15895
  have eq16012 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15954 eq15987
    | exact resolve eq15987 eq15954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15954 eq15987
  have eq16109 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq16012 eq27
    | exact resolve eq27 eq16012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16012
  have eq16190 : False := by grind
  exact eq16190

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
    grind
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
  have eq24 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq9 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq24 X1 X0
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq24 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq98 X0
       have j1 := eq69 X0 X0 X0
       grind)
    | (have r₁ := eq98 X0
       have r₂ := eq69 X0 (k X0 X0) x
       grind)
    | (have r₁ := eq98 x
       have r₂ := eq69 x x x
       grind)
    | (have r₁ := eq98 (M.op X0 X0)
       have r₂ := eq69 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact resolve eq98 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq98
  have eq109 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq107 (σ X0)
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq109
    | exact resolve eq109 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq109
  have eq131 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq136 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq162 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2173 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq136 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq136 X0 X1
       grind)
    | exact superpose eq136 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq136 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq136 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq136 X0 X1
       grind)
    | exact resolve eq13 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq2195 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2201 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2195 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2195 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq2195 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2207 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2201 X0 X1
       have j1 := eq162 X0 (σ X1)
       grind)
    | (have r₁ := eq2201 X0 X1
       have r₂ := eq162 X0 X1
       grind)
    | exact resolve eq2201 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq2201
  have eq2213 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2207 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2207
    | (have j0 := eq2207 X0 X1
       grind)
    | exact resolve eq2207 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq2214 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2223 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2214 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2214
    | exact resolve eq2214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2254 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2214 x y
       grind)
    | exact superpose eq2214 eq16
    | exact resolve eq16 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq3697 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq2223 X0 (τ X1)
       grind)
    | exact superpose eq2223 eq17
    | exact resolve eq17 eq2223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2223
  have eq3711 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3697 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3697
    | exact resolve eq3697 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3697
  have eq3733 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3711 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3711
    | exact resolve eq3711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3711
  have eq3983 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2254
       have i₂ := eq3733 x y
       grind)
    | exact superpose eq3733 eq2254
    | exact resolve eq2254 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254 eq3733
  have eq3984 : False := by grind
  exact eq3984
