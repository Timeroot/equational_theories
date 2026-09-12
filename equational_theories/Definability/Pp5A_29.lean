import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxx_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq9 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq21 X0 x X2
       have i₂ := eq9 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq21 X0 x X2
       have i₂ := eq9 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (M.op X0 X0)
       have i₂ := eq36 X1 (M.op X0 X0)
       grind)
    | exact superpose eq36 eq22
    | exact resolve eq22 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq36 X1 (τ X0)
       grind)
    | exact superpose eq36 eq18
    | exact resolve eq18 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq36
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq149 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq58 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq58 X0
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq152 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq149 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq149 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq283 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq16
    | (have j1 := eq90 x y
       grind)
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq1289 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq152 (M.op X0 X0) X1
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq152
    | (have j0 := eq152 (M.op X0 X0) X1
       grind)
    | exact resolve eq152 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq152
  have eq1298 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1397 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq48 X0 x
       have i₂ := eq1298 x X0
       grind)
    | exact superpose eq1298 eq48
    | exact resolve eq48 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1298
  have eq1426 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1397 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1397
    | exact resolve eq1397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1618 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) x
       have i₂ := eq1426 X0
       grind)
    | exact superpose eq1426 eq22
    | exact resolve eq22 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3099 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq283
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq283
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq283
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq283
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq283 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq3100 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq3099
  have eq3101 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3100
       have i₂ := eq1426 y
       grind)
    | exact superpose eq1426 eq3100
    | exact resolve eq3100 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3100
  have eq58337 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3101
       grind)
    | exact superpose eq3101 eq16
    | exact resolve eq16 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq58338 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq58337
       have r₂ := eq1426 x
       grind)
    | exact resolve eq58337 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58337
  have eq1413163 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq58338
       grind)
    | exact superpose eq58338 eq10
    | exact resolve eq10 eq58338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58338
  have eq1413483 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1413163
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1413163
    | exact resolve eq1413163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413163
  have eq1413563 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1413483
       grind)
    | exact superpose eq1413483 eq16
    | exact resolve eq16 eq1413483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413483
  have eq1413564 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1413563
       have r₂ := eq1426 x
       grind)
    | exact resolve eq1413563 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426 eq1413563
  have eq1413746 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1413564
       grind)
    | exact superpose eq1413564 eq10
    | exact resolve eq10 eq1413564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413564
  have eq1414075 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1413746
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1413746
    | exact resolve eq1413746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413746
  have eq1414076 : y = (M.op y y) := by grind
  clear eq1414075
  have eq1417647 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq22 y x
       have i₂ := eq1414076
       grind)
    | exact superpose eq1414076 eq22
    | exact resolve eq22 eq1414076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1417749 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1618 y x
       have i₂ := eq1414076
       grind)
    | exact superpose eq1414076 eq1618
    | exact resolve eq1618 eq1414076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq1414076
  have eq1431178 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1417749 (σ x)
       grind)
    | exact superpose eq1417749 eq16
    | exact resolve eq16 eq1417749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417749
  have eq1431207 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1431178
       have i₂ := eq1417647 x
       grind)
    | exact superpose eq1417647 eq1431178
    | exact resolve eq1431178 eq1417647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417647 eq1431178
  have eq1431208 : False := by grind
  exact eq1431208

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyy_Equation3506 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 (M.op (M.op x x) x) x x
       have i₂ := eq9 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq29 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq29 X0 X1
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq31 (σ X0) (σ X1)
       grind)
    | exact superpose eq31 eq15
    | (have j1 := eq31 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29
  have eq243 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq31 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq5171 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq243 x y
       grind)
    | exact superpose eq243 eq16
    | (have j1 := eq243 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq243 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq243 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq243 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq5189 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq5171
  have eq8007 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5189
       grind)
    | exact superpose eq5189 eq10
    | exact resolve eq10 eq5189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5189
  have eq8028 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8007
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8007
    | exact resolve eq8007 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8007
  have eq8029 : x = y := by grind
  clear eq8028
  have eq14987 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8029
       grind)
    | exact superpose eq8029 eq16
    | exact resolve eq16 eq8029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8029
  have eq14988 : False := by grind
  exact eq14988

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxx_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X1) X1) X1
       have r₂ := eq9 X1 X1 X2
       grind)
    | exact resolve eq12 eq9
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
  have eq61 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq22
    | exact resolve eq22 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq84 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq83
    | exact resolve eq83 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq84
    | exact resolve eq84 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq84
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq10
    | exact resolve eq10 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq117 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq25 X0 X1 (M.op (M.op X2 X1) X0) X2
       grind)
    | exact superpose eq25 eq34
    | (have j0 := eq34 X0 X1 X2
       grind)
    | (have r₁ := eq34 (M.op (M.op x X1) X0) X1 X2
       have r₂ := eq25 X0 X1 (M.op (M.op x X1) X0) x
       grind)
    | (have r₁ := eq34 X1 (M.op (M.op x X1) X0) X2
       have r₂ := eq25 X0 X1 X1 x
       grind)
    | exact resolve eq34 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq131 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X1) = (M.op (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq164 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (σ X0) X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq25
    | exact resolve eq25 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq102
  have eq594 : ∀ X0 X1 : G, (k (σ (M.op (M.op X0 (τ X1)) (τ X1))) X1) = (σ (M.op (M.op (M.op X0 (τ X1)) (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op (M.op X0 (τ X1)) (τ X1))
       have i₂ := eq131 X0 (τ X1)
       grind)
    | exact superpose eq131 eq18
    | exact resolve eq18 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq131
  have eq5324 : ∀ X0 X1 : G, (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) ∨ (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ X1) (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq469 (M.op X0 (τ X1)) X1
       grind)
    | exact superpose eq469 eq594
    | (have j1 := eq469 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq594 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq5370 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ X1) (M.op X0 (τ X1))) ∨ (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5324
  have eq182536 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (M.op X1 X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5370 X0 X1
       have i₂ := eq469 X0 X1
       grind)
    | exact superpose eq469 eq5370
    | (have j1 := eq469 X0 X1
       grind)
    | exact resolve eq5370 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq5370
  have eq182674 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq182536 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182536
  have eq182818 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq182674 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182674
    | exact resolve eq182674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182674
  have eq183310 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq182818 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq182818
    | (have j0 := eq182818 X0 X1
       grind)
    | exact resolve eq182818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182818
  have eq183356 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq183310 X0 X1
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq183310
    | (have j0 := eq183310 X0 X1
       grind)
    | exact resolve eq183310 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq183310
  have eq184249 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq183356 X1 X0
       grind)
    | exact superpose eq183356 eq10
    | (have j1 := eq183356 X1 X0
       grind)
    | exact resolve eq10 eq183356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184566 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq184249 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq184249
    | (have j0 := eq184249 X0 X1
       grind)
    | exact resolve eq184249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184249
  have eq185819 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq184566 (σ X0) (σ X1)
       grind)
    | exact superpose eq184566 eq15
    | (have j1 := eq184566 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq184566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186091 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq185819 X0 X1
       have i₂ := eq95 X1
       grind)
    | exact superpose eq95 eq185819
    | (have j0 := eq185819 X0 X1
       grind)
    | exact resolve eq185819 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185819
  have eq212010 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq186091 x y
       grind)
    | exact superpose eq186091 eq16
    | (have j1 := eq186091 x y
       grind)
    | exact resolve eq16 eq186091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186091
  have eq213005 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq212010
       have i₂ := eq183356 y x
       grind)
    | exact superpose eq183356 eq212010
    | (have j1 := eq183356 y x
       grind)
    | (have r₁ := eq212010
       have r₂ := eq183356 y x
       grind)
    | exact resolve eq212010 eq183356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183356
  have eq213012 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq213005
  have eq213361 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq168 y (σ x)
       have i₂ := eq213012
       grind)
    | exact superpose eq213012 eq168
    | (have j0 := eq168 y (σ x)
       grind)
    | (have r₁ := eq168 y (σ x)
       have r₂ := eq213012
       grind)
    | exact resolve eq168 eq213012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq213012
  have eq213448 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq213361
  have eq213484 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq213448
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq213448
    | exact resolve eq213448 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213448
  have eq213516 : (M.op y y) = (M.op y x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq213484
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq213484
    | exact resolve eq213484 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213484
  have eq216024 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 y
       have i₂ := eq213516
       grind)
    | exact superpose eq213516 eq25
    | exact resolve eq25 eq213516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213516
  have eq216060 : ∀ X0 : G, (σ (k x y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq216024 X0 x
       have i₂ := eq25 x x X0 y
       grind)
    | exact superpose eq25 eq216024
    | exact resolve eq216024 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216024
  have eq218296 : ∀ X0 : G, (k x y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq216060 X0
       grind)
    | exact superpose eq216060 eq10
    | (have j1 := eq216060 X0
       grind)
    | exact resolve eq10 eq216060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216060
  have eq218633 : ∀ X0 : G, (k x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq218296 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq218296
    | (have j0 := eq218296 X0
       grind)
    | exact resolve eq218296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218296
  have eq220175 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq218633 X0
       have i₂ := eq184566 x y
       grind)
    | exact superpose eq184566 eq218633
    | (have j0 := eq218633 x
       have j1 := eq184566 y x
       grind)
    | exact resolve eq218633 eq184566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184566 eq218633
  have eq300922 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have j0 := eq220175 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220175
  have eq300923 : (M.op x y) = (M.op x x) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq300922
  have eq300950 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op y y) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 x
       have i₂ := eq300923
       grind)
    | exact superpose eq300923 eq25
    | exact resolve eq25 eq300923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300923
  have eq301011 : ∀ X0 : G, (M.op y y) = (M.op y x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq300950 X0 x
       have i₂ := eq25 x x X0 x
       grind)
    | exact superpose eq25 eq300950
    | exact resolve eq300950 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300950
  have eq301251 : (M.op y x) ≠ (M.op y x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have j0 := eq301011 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301011
  have eq301252 : (M.op y y) = (M.op y x) := by grind
  clear eq301251
  have eq301259 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq301252
       grind)
    | exact superpose eq301252 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq301252
       grind)
    | exact resolve eq12 eq301252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301262 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq164 y X0 X1
       have i₂ := eq301252
       grind)
    | exact superpose eq301252 eq164
    | exact resolve eq164 eq301252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq301390 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 y X0 y
       have i₂ := eq301252
       grind)
    | exact superpose eq301252 eq25
    | exact resolve eq25 eq301252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301252
  have eq301427 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq301390 X0 x
       have i₂ := eq25 x x X0 y
       grind)
    | exact superpose eq25 eq301390
    | exact resolve eq301390 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq301390
  have eq314895 : (k x y) = (M.op x x) := by
    first
    | (have j0 := eq301259 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301259
  have eq314960 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq212010
       have i₂ := eq314895
       grind)
    | exact superpose eq314895 eq212010
    | exact resolve eq212010 eq314895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212010 eq314895
  have eq315040 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq314960
       have i₂ := eq301427 x
       grind)
    | exact superpose eq301427 eq314960
    | exact resolve eq314960 eq301427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314960
  have eq315041 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by grind
  clear eq315040
  have eq315048 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq315041
       have i₂ := eq301427 y
       grind)
    | exact superpose eq301427 eq315041
    | exact resolve eq315041 eq301427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315041
  have eq315120 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op y x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq315048
       grind)
    | exact superpose eq315048 eq9
    | exact resolve eq9 eq315048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315048
  have eq315181 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq315120 X0
       have i₂ := eq301262 X0 X0
       grind)
    | exact superpose eq301262 eq315120
    | exact resolve eq315120 eq301262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301262 eq315120
  have eq315661 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq315181 (σ x)
       grind)
    | exact superpose eq315181 eq16
    | exact resolve eq16 eq315181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315181
  have eq315819 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq315661
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq315661
    | exact resolve eq315661 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq315661
  have eq316177 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq315819
       have i₂ := eq301427 x
       grind)
    | exact superpose eq301427 eq315819
    | exact resolve eq315819 eq301427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301427 eq315819
  have eq316178 : False := by grind
  exact eq316178

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_y_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op (M.op X2 X1) X0) X0) = (k (M.op (M.op X2 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X1) X1) X1
       have r₂ := eq9 X1 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq57
    | (have j0 := eq57 (σ X0) (σ X1)
       grind)
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq57 X0 (τ X1)
       grind)
    | exact superpose eq57 eq18
    | (have j1 := eq57 X0 (τ X1)
       grind)
    | exact resolve eq18 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq126 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  clear eq68
  have eq156 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X1) = (k (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq870 : ∀ X0 X1 : G, (k (τ (M.op (M.op X0 (σ X1)) (σ X1))) X1) = (τ (M.op (M.op (M.op X0 (σ X1)) (σ X1)) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (M.op X0 (σ X1)) (σ X1)) X1
       have i₂ := eq156 X0 (σ X1)
       grind)
    | exact superpose eq156 eq22
    | exact resolve eq22 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 X1 : G, (k (σ (M.op (M.op X0 (τ X1)) (τ X1))) X1) = (σ (M.op (M.op (M.op X0 (τ X1)) (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op (M.op X0 (τ X1)) (τ X1))
       have i₂ := eq156 X0 (τ X1)
       grind)
    | exact superpose eq156 eq18
    | exact resolve eq18 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq156
  have eq5988 : ∀ X0 X1 : G, (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) ∨ (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0 X1
       have i₂ := eq74 (M.op X0 (τ X1)) X1
       grind)
    | exact superpose eq74 eq872
    | (have j1 := eq74 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq872 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq6045 : ∀ X0 X1 : G, (k (σ (M.op X0 (τ X1))) X1) = (σ (M.op (M.op X0 (τ X1)) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5988 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5988
  have eq6096 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6045 X0 X1
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq6045
    | (have j1 := eq74 X0 X1
       grind)
    | exact resolve eq6045 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq6045
  have eq6156 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq6096 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6096
  have eq6246 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6156 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6156
    | exact resolve eq6156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6156
  have eq6559 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq6246 X1 X0
       grind)
    | exact superpose eq6246 eq22
    | exact resolve eq22 eq6246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6246
  have eq6593 : ∀ X0 X1 : G, (M.op X0 X1) = (k (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6559 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq6559
    | exact resolve eq6559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6559
  have eq6621 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6593 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6593
    | exact resolve eq6593 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6593
  have eq6717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq126
       have i₂ := eq6621 x y
       grind)
    | exact superpose eq6621 eq126
    | exact resolve eq126 eq6621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq6718 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6717
  have eq6898 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6718
       grind)
    | exact superpose eq6718 eq16
    | exact resolve eq16 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6901 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have i₁ := eq870 (σ x) y
       have i₂ := eq6718
       grind)
    | exact superpose eq6718 eq870
    | exact resolve eq870 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq6923 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have i₁ := eq6901
       have i₂ := eq6621 (τ (M.op (σ x) (σ y))) y
       grind)
    | exact superpose eq6621 eq6901
    | exact resolve eq6901 eq6621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6621 eq6901
  have eq6928 : (τ (M.op (σ x) (σ y))) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq6923
       have i₂ := eq6718
       grind)
    | exact superpose eq6718 eq6923
    | exact resolve eq6923 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6923
  have eq6932 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6928
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6928
    | exact resolve eq6928 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6928
  have eq6933 : (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq6932
       have i₂ := eq6718
       grind)
    | exact superpose eq6718 eq6932
    | exact resolve eq6932 eq6718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6718 eq6932
  have eq6934 : x = (M.op x y) := by
    first
    | (have i₁ := eq6933
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6933
    | exact resolve eq6933 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6933
  have eq6970 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6898
       have i₂ := eq6934
       grind)
    | exact superpose eq6934 eq6898
    | exact resolve eq6898 eq6934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6898 eq6934
  have eq6971 : False := by grind
  exact eq6971

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxx_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq13 X0 X0
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
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
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
  have eq175 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X1 X2 X3
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq187 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq189 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq16 X1 y X0
       grind)
    | exact superpose eq16 eq187
    | exact resolve eq187 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq194 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq197 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq194 x X0
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq194
    | exact resolve eq194 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq872 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq877 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : (M.op x y) ≠ (k x x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq872
       have i₂ := eq877 x
       grind)
    | exact superpose eq877 eq872
    | exact resolve eq872 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq892 : (M.op x y) ≠ (k x x) ∨ (k y x) = (k y y) := by
    first
    | (have i₁ := eq882
       have i₂ := eq877 y
       grind)
    | exact superpose eq877 eq882
    | exact resolve eq882 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq916 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq941 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq916 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq962 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq941 X0 X1 X2
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq941
    | (have j0 := eq941 X0 X1 X2
       grind)
    | exact resolve eq941 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq976 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq956 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq956 X1 X0
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq956 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq999 : ∀ X0 X1 : G, (k X1 X0) = (k X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq976 X0 X1
       have i₂ := eq877 X1
       grind)
    | exact superpose eq877 eq976
    | (have j0 := eq976 X0 X1
       grind)
    | exact resolve eq976 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1007 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op (k X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X2 X0 X1 X0
       have i₂ := eq877 X0
       grind)
    | exact superpose eq877 eq179
    | exact resolve eq179 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op X0 X1) X1 X2 X0
       have i₂ := eq877 (M.op X0 X1)
       grind)
    | exact superpose eq877 eq179
    | exact resolve eq179 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1956 : (k x y) = (τ (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq999 sF3 sF2
       grind)
    | exact superpose eq999 eq99
    | (have j1 := eq999 (σ y) (σ x)
       grind)
    | exact resolve eq99 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq2034 : (k x x) = (k x y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq98 eq1956
    | exact resolve eq1956 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq2091 : (k x x) = (k x y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2034
    | exact resolve eq2034 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034
  have eq2114 : (σ (k x x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq2091
       grind)
    | exact superpose eq2091 eq41
    | exact resolve eq41 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2115 : (σ (k x x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2114
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2114
    | exact resolve eq2114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114
  have eq2117 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2115
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq2115
    | exact resolve eq2115 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq2119 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2117
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2117
    | exact resolve eq2117 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117
  have eq8190 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq962 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq8191 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8190 X0 X1
       have i₂ := eq877 X0
       grind)
    | exact superpose eq877 eq8190
    | (have j0 := eq8190 X0 X1
       grind)
    | (have r₁ := eq8190 X0 X0
       have r₂ := eq877 X0
       grind)
    | exact resolve eq8190 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8190
  have eq8281 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8191 X0 X1
       have j1 := eq999 X1 X0
       grind)
    | (have r₁ := eq8191 X1 X0
       have r₂ := eq999 X0 X1
       grind)
    | (have r₁ := eq8191 X0 X0
       have r₂ := eq999 X0 X0
       grind)
    | exact resolve eq8191 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq8191
  have eq8421 : (M.op x y) = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8281 x y
       grind)
    | exact superpose eq8281 eq18
    | (have j1 := eq8281 x y
       grind)
    | exact resolve eq18 eq8281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8430 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq8281 sF2 sF3
       grind)
    | exact superpose eq8281 eq26
    | (have j1 := eq8281 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq8281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8463 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq8421
       grind)
    | exact superpose eq8421 eq41
    | exact resolve eq41 eq8421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8421
  have eq8465 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8463
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8463
    | exact resolve eq8463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8463
  have eq8469 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq8465
    | exact resolve eq8465 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8465
  have eq8486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8469 eq8430
    | exact resolve eq8430 eq8469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8489 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8469 eq2119
    | exact resolve eq2119 eq8469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119 eq8469
  have eq8498 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq8489
       have r₂ := eq27
       grind)
    | exact resolve eq8489 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8489
  have eq8501 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq8486
       have r₂ := eq27
       grind)
    | exact resolve eq8486 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8486
  have eq8522 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8501 eq8281
    | (have j0 := eq8281 (σ y) (σ x)
       grind)
    | exact resolve eq8281 eq8501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8281 eq8501
  have eq8525 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq8522
    | exact resolve eq8522 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8522
  have eq8538 : (τ (σ (M.op x y))) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8498 eq98
    | exact resolve eq98 eq8498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq8549 : (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq8538
    | exact resolve eq8538 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8538
  have eq8557 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq892
       have i₂ := eq8549
       grind)
    | exact superpose eq8549 eq892
    | (have r₁ := eq892
       have r₂ := eq8549
       grind)
    | exact resolve eq892 eq8549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq8565 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1007 x X0 X1
       have i₂ := eq8549
       grind)
    | exact superpose eq8549 eq1007
    | exact resolve eq1007 eq8549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8549
  have eq8566 : (k y x) = (k y y) ∨ y = (M.op y x) := by grind
  clear eq8557
  have eq8567 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq189 eq8565
    | exact resolve eq8565 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq8565
  have eq8610 : (k y y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq877 y
       have i₂ := eq8567 y
       grind)
    | exact superpose eq8567 eq877
    | exact resolve eq877 eq8567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8567
  have eq8649 : (k y x) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8566 eq8610
    | exact resolve eq8610 eq8566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8566 eq8610
  have eq8683 : y ≠ (k y x) ∨ y = (M.op y x) := by grind
  clear eq8649
  have eq8690 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8525 eq142
    | exact resolve eq142 eq8525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8525
  have eq8691 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq8690
    | exact resolve eq8690 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq8690
  have eq8696 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8691
       have r₂ := eq8683
       grind)
    | exact resolve eq8691 eq8683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8683 eq8691
  have eq8707 : y ≠ y ∨ (k x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq8696
       grind)
    | exact superpose eq8696 eq28
    | (have j0 := eq28 x y
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq8696
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq8696
       grind)
    | exact resolve eq28 eq8696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8708 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 x X0 y
       have i₂ := eq8696
       grind)
    | exact superpose eq8696 eq179
    | exact resolve eq179 eq8696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8716 : (k x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8707
  have eq8719 : (k x x) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8716
       have i₂ := eq877 x
       grind)
    | exact superpose eq877 eq8716
    | exact resolve eq8716 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8716
  have eq8727 : (σ (k x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq8719
       grind)
    | exact superpose eq8719 eq41
    | exact resolve eq41 eq8719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8719
  have eq8728 : (σ (k x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8727
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8727
    | exact resolve eq8727 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8727
  have eq8732 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8728
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq8728
    | exact resolve eq8728 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8728
  have eq8734 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8732
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8732
    | exact resolve eq8732 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8732
  have eq8741 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8734 eq8430
    | exact resolve eq8430 eq8734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8430 eq8734
  have eq8776 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8708 X0 x
       have i₂ := eq8696
       grind)
    | exact superpose eq8696 eq8708
    | exact resolve eq8708 eq8696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8708
  have eq8834 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8776
  have eq8853 : (k y y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq877 y
       have i₂ := eq8834 y
       grind)
    | exact superpose eq8834 eq877
    | exact resolve eq877 eq8834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8872 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8834 x
       grind)
    | exact superpose eq8834 eq18
    | (have j1 := eq8834 x
       grind)
    | exact resolve eq18 eq8834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8834
  have eq8885 : (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8872
       have i₂ := eq877 x
       grind)
    | exact superpose eq877 eq8872
    | exact resolve eq8872 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8872
  have eq8894 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8696 eq8853
    | exact resolve eq8853 eq8696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8696 eq8853
  have eq8905 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq8885
       grind)
    | exact superpose eq8885 eq40
    | exact resolve eq40 eq8885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq8885
  have eq8917 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8905
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8905
    | exact resolve eq8905 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8905
  have eq8923 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8917
    | exact resolve eq8917 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8917
  have eq8931 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq8894
       grind)
    | exact superpose eq8894 eq41
    | exact resolve eq41 eq8894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq8894
  have eq8943 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8931
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8931
    | exact resolve eq8931 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8931
  have eq9564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8741 eq8923
    | exact resolve eq8923 eq8741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8741
  have eq9573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq9564
  have eq9583 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9573
       have r₂ := eq27
       grind)
    | exact resolve eq9573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9573
  have eq9609 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9583 eq1014
    | exact resolve eq1014 eq9583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq9583
  have eq9615 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8943 eq9609
    | exact resolve eq9609 eq8943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8943 eq9609
  have eq9654 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9615 eq26
    | (have j1 := eq9615 (σ x)
       grind)
    | exact resolve eq26 eq9615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9615
  have eq9663 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9654
       have i₂ := eq877 sF2
       grind)
    | exact superpose eq877 eq9654
    | exact resolve eq9654 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9654
  have eq9676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8923 eq9663
    | exact resolve eq9663 eq8923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8923 eq9663
  have eq9681 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9676
       have r₂ := eq27
       grind)
    | exact resolve eq9676 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9676
  have eq9684 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9681 eq27
    | exact resolve eq27 eq9681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq9689 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq9681 eq197
    | exact resolve eq197 eq9681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq9778 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq9689
    | (have j0 := eq9689 X0 (σ y)
       grind)
    | exact resolve eq9689 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9689
  have eq9859 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq9681 eq9778
    | exact resolve eq9778 eq9681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9778
  have eq9901 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9859 eq26
    | (have j1 := eq9859 (σ x)
       grind)
    | exact resolve eq26 eq9859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9859
  have eq9909 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9901
       have i₂ := eq877 sF2
       grind)
    | exact superpose eq877 eq9901
    | exact resolve eq9901 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9901
  have eq9922 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq9681 eq9909
    | exact resolve eq9909 eq9681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9681 eq9909
  have eq9937 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9922 eq8498
    | exact resolve eq8498 eq9922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8498
  have eq9941 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | exact superpose eq9922 eq142
    | exact resolve eq142 eq9922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq9922
  have eq9951 : x = (k x x) := by
    first
    | exact superpose eq30 eq9941
    | exact resolve eq9941 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9941
  have eq9953 : y = (M.op y x) := by
    first
    | (have r₁ := eq9937
       have r₂ := eq9684
       grind)
    | exact resolve eq9937 eq9684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9937
  have eq9975 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1007 x X0 X1
       have i₂ := eq9951
       grind)
    | exact superpose eq9951 eq1007
    | exact resolve eq1007 eq9951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq9994 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 x X0 y
       have i₂ := eq9953
       grind)
    | exact superpose eq9953 eq179
    | exact resolve eq179 eq9953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq10292 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq9975 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9975
    | (have j0 := eq9975 X0 y
       grind)
    | exact resolve eq9975 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9975
  have eq10402 : (k x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq877 x
       have i₂ := eq10292 x
       grind)
    | exact superpose eq10292 eq877
    | exact resolve eq877 eq10292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq10427 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq9953
       have i₂ := eq10292 y
       grind)
    | exact superpose eq10292 eq9953
    | exact resolve eq9953 eq10292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9953
  have eq10454 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq10402
       have i₂ := eq9951
       grind)
    | exact superpose eq9951 eq10402
    | exact resolve eq10402 eq9951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9951 eq10402
  have eq10877 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq10427 eq9994
    | exact resolve eq9994 eq10427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9994 eq10427
  have eq10980 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq10877 X0
       have i₂ := eq10292 X0
       grind)
    | exact superpose eq10292 eq10877
    | exact resolve eq10877 eq10292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10292 eq10877
  have eq11033 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10980 x
       grind)
    | exact superpose eq10980 eq18
    | (have j1 := eq10980 x
       grind)
    | exact resolve eq18 eq10980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10980
  have eq11073 : x = (M.op x y) := by
    first
    | exact superpose eq11033 eq10454
    | exact resolve eq10454 eq11033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10454 eq11033
  have eq11097 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq11073
       grind)
    | exact superpose eq11073 eq22
    | exact resolve eq22 eq11073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11073
  have eq11153 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11097 eq20
    | exact resolve eq20 eq11097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11097
  have eq11247 : False := by grind
  exact eq11247

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxx_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) X0) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X1) X1) X1
       have r₂ := eq14 X1 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq73 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq14 X0 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq95 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X0 X1 X2
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq89
    | (have j0 := eq89 X0 X1 X2
       grind)
    | exact resolve eq89 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq116 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq117 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq119 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq117
    | exact resolve eq117 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq119
    | exact resolve eq119 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq119
  have eq127 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq16
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq254
    | exact resolve eq254 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1005 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1446 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X2 X1) X0) X0) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 X1 X2
       have i₂ := eq54 X0 X1 (M.op (M.op X2 X1) X0) X2
       grind)
    | exact superpose eq54 eq66
    | (have j0 := eq66 X0 X1 X2
       grind)
    | (have r₁ := eq66 (M.op (M.op x X1) X0) X1 X2
       have r₂ := eq54 X0 X1 (M.op (M.op x X1) X0) x
       grind)
    | (have r₁ := eq66 X1 (M.op (M.op x X1) X0) X2
       have r₂ := eq54 X0 X1 X1 x
       grind)
    | exact resolve eq66 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1516 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) X1) = (M.op (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1446 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq4473 : (k (M.op (M.op x y) y) y) = (M.op (M.op (M.op x y) y) y) := by
    first
    | (have i₁ := eq1516 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1516
    | (have j0 := eq1516 x y
       grind)
    | exact resolve eq1516 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4474 : (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq1516
    | (have j0 := eq1516 (σ x) (σ y)
       grind)
    | exact resolve eq1516 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq5948 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1005 X0 X1
       have j1 := eq95 X1 X0 x
       grind)
    | (have r₁ := eq1005 X0 X1
       have r₂ := eq95 X0 X1 X0
       grind)
    | (have r₁ := eq1005 X1 X0
       have r₂ := eq95 X0 X1 X1
       grind)
    | exact resolve eq1005 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq1005
  have eq6102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq5948 x y
       grind)
    | exact superpose eq5948 eq44
    | (have j1 := eq5948 x y
       grind)
    | exact resolve eq44 eq5948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6239 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6102
    | exact resolve eq6102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6102
  have eq6259 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq6239
    | exact resolve eq6239 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6239
  have eq6278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6259 eq5948
    | (have j0 := eq5948 (σ x) (σ y)
       grind)
    | exact resolve eq5948 eq6259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6259
  have eq6282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq6278
    | exact resolve eq6278 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6278
  have eq6294 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq6282
       have r₂ := eq27
       grind)
    | exact resolve eq6282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6282
  have eq6303 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq6294 eq14
    | exact resolve eq14 eq6294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6313 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6294 eq6303
    | exact resolve eq6303 eq6294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6303
  have eq6349 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq6313
  have eq6352 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq6349
    | exact resolve eq6349 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6349
  have eq6356 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6352 eq65
    | (have r₁ := eq65
       have r₂ := eq6352
       grind)
    | exact resolve eq65 eq6352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq6366 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq6352 eq54
    | exact resolve eq54 eq6352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6352
  have eq6380 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq6356
  have eq6382 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq257 eq6366
    | exact resolve eq6366 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq6366
  have eq6429 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6380 eq127
    | exact resolve eq127 eq6380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq6380
  have eq6446 : (k y x) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq153 eq6429
    | exact resolve eq6429 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6429
  have eq6477 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6382 eq153
    | exact resolve eq153 eq6382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq6382
  have eq6506 : (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5948 y x
       have i₂ := eq6446
       grind)
    | exact superpose eq6446 eq5948
    | (have j0 := eq5948 y x
       grind)
    | exact resolve eq5948 eq6446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6446
  have eq6508 : (M.op y y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6506
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6506
    | exact resolve eq6506 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6506
  have eq6519 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6294 eq6477
    | exact resolve eq6477 eq6294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6294 eq6477
  have eq6550 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq6519
  have eq6555 : y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq6550
    | exact resolve eq6550 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6550
  have eq7779 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6555
       have i₂ := eq6508
       grind)
    | exact superpose eq6508 eq6555
    | exact resolve eq6555 eq6508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6508 eq6555
  have eq7820 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq7779
  have eq7829 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq7820
       grind)
    | exact superpose eq7820 eq14
    | exact resolve eq14 eq7820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7843 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7829 x
       have i₂ := eq7820
       grind)
    | exact superpose eq7820 eq7829
    | exact resolve eq7829 eq7820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7820 eq7829
  have eq7907 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq7843
  have eq7912 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7907
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7907
    | exact resolve eq7907 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7907
  have eq7917 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq7912
       grind)
    | exact superpose eq7912 eq64
    | (have r₁ := eq64
       have r₂ := eq7912
       grind)
    | exact resolve eq64 eq7912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq7918 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq7912
       grind)
    | exact superpose eq7912 eq73
    | exact resolve eq73 eq7912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7912
  have eq7957 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq7917
  have eq7969 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq7918
    | exact resolve eq7918 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7918
  have eq8029 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq7957
       grind)
    | exact superpose eq7957 eq116
    | exact resolve eq116 eq7957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq7957
  have eq8049 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8029
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq8029
    | exact resolve eq8029 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq8029
  have eq8169 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8049 eq5948
    | (have j0 := eq5948 (σ y) (σ x)
       grind)
    | exact resolve eq5948 eq8049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8049
  have eq8171 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8169
    | exact resolve eq8169 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8169
  have eq10214 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8171 eq54
    | exact resolve eq54 eq8171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171
  have eq10239 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10214 x X0
       have i₂ := eq54 X0 sF2 x sF3
       grind)
    | exact superpose eq54 eq10214
    | exact resolve eq10214 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10214
  have eq10267 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10239
    | (have j0 := eq10239 (σ x)
       grind)
    | exact resolve eq10239 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10239
  have eq10388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10267 eq7969
    | exact resolve eq7969 eq10267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10267
  have eq10417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10388
  have eq10430 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10417
       have r₂ := eq27
       grind)
    | exact resolve eq10417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10417
  have eq10433 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10430 eq51
    | exact resolve eq51 eq10430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq10440 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10430 eq4474
    | exact resolve eq4474 eq10430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4474
  have eq10445 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10440
    | exact resolve eq10440 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10440
  have eq10607 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10430 eq10445
    | exact resolve eq10445 eq10430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10445
  have eq10609 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10607
  have eq10610 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10609
    | exact resolve eq10609 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10609
  have eq10653 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10433
    | (have j0 := eq10433 (σ y)
       grind)
    | exact resolve eq10433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10433
  have eq10819 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10653 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq10653
       grind)
    | exact resolve eq13 eq10653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10653
  have eq10833 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10819
  have eq11007 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10430 eq10833
    | exact resolve eq10833 eq10430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10430 eq10833
  have eq11018 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11007
  have eq11641 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11018 eq10610
    | exact resolve eq10610 eq11018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10610 eq11018
  have eq11645 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11641
  have eq11671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11645 eq7969
    | exact resolve eq7969 eq11645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7969 eq11645
  have eq11702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11671
  have eq11714 : x = (M.op x y) := by
    first
    | (have r₁ := eq11702
       have r₂ := eq27
       grind)
    | exact resolve eq11702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11702
  have eq11716 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq11714 eq20
    | exact resolve eq20 eq11714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq11718 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq11714 eq50
    | exact resolve eq50 eq11714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq11774 : (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq11714 eq4473
    | exact resolve eq4473 eq11714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4473
  have eq11781 : (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq11774
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11774
    | exact resolve eq11774 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11774
  have eq11832 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11716
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11716
    | exact resolve eq11716 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11716
  have eq11833 : (M.op x y) = (k x y) := by
    first
    | exact superpose eq11714 eq11781
    | exact resolve eq11781 eq11714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11781
  have eq11848 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq11833
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11833
    | exact resolve eq11833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11833
  have eq11849 : x = (k x y) := by
    first
    | exact superpose eq11714 eq11848
    | exact resolve eq11848 eq11714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11848
  have eq11850 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11832 eq26
    | exact resolve eq26 eq11832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq12169 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11849
       grind)
    | exact superpose eq11849 eq44
    | exact resolve eq44 eq11849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq11849
  have eq12190 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11832 eq12169
    | exact resolve eq12169 eq11832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12169
  have eq12199 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq12190
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12190
    | exact resolve eq12190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12190
  have eq12205 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11832 eq12199
    | exact resolve eq12199 eq11832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12199
  have eq12258 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12205 eq5948
    | (have j0 := eq5948 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq5948 eq12205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5948 eq12205
  have eq12262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq11850 eq12258
    | exact resolve eq12258 eq11850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12258
  have eq12274 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq12262
       have r₂ := eq27
       grind)
    | exact resolve eq12262 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12262
  have eq12302 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq12274 eq14
    | exact resolve eq14 eq12274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12413 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq11718 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11718
    | (have j0 := eq11718 y
       grind)
    | exact resolve eq11718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11718
  have eq12530 : (M.op y y) = (M.op y x) := by
    first
    | exact superpose eq11714 eq12413
    | exact resolve eq12413 eq11714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12413
  have eq12609 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq12530
       grind)
    | exact superpose eq12530 eq54
    | exact resolve eq54 eq12530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12530
  have eq12629 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq12609 X0 x
       have i₂ := eq54 x x X0 y
       grind)
    | exact superpose eq54 eq12609
    | exact resolve eq12609 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq12609
  have eq12716 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12629 x
       grind)
    | exact superpose eq12629 eq18
    | (have j1 := eq12629 x
       grind)
    | exact resolve eq18 eq12629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq12629
  have eq12782 : x = (M.op x x) := by
    first
    | exact superpose eq11714 eq12716
    | exact resolve eq12716 eq11714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11714 eq12716
  have eq12862 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq12782
       grind)
    | exact superpose eq12782 eq73
    | exact resolve eq73 eq12782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq12782
  have eq12924 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11832 eq12862
    | exact resolve eq12862 eq11832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12862
  have eq12933 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12924
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12924
    | exact resolve eq12924 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12924
  have eq12942 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11832 eq12933
    | exact resolve eq12933 eq11832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11832 eq12933
  have eq13631 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12274 eq12302
    | exact resolve eq12302 eq12274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12274 eq12302
  have eq13775 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11850 eq13631
    | exact resolve eq13631 eq11850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11850 eq13631
  have eq13786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12942 eq13775
    | exact resolve eq13775 eq12942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12942 eq13775
  have eq13793 : False := by grind
  exact eq13793

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq39 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
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
  clear eq37
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq40
    | exact resolve eq40 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq99 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq115 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X0) X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq21
    | exact resolve eq21 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op (M.op X0 X1) X2) X1) ∨ (M.op X3 (M.op (M.op X0 X1) X2)) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op (M.op X0 X1) X2)
       have i₂ := eq21 X2 X1 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X3 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq21 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq21 X0 X1 X1 X3
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (k X3 (M.op (M.op X0 X1) X2)) ∨ (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op (M.op X0 X1) X2) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq151 X0 X1 X2 X3
       have i₂ := eq21 X2 X1 X3 X0
       grind)
    | exact superpose eq21 eq151
    | (have j0 := eq151 X0 X1 X2 X3
       grind)
    | (have r₁ := eq151 X0 (M.op (M.op X3 X1) X0) X2 X1
       have r₂ := eq21 X0 X1 (M.op (M.op X0 (M.op (M.op X3 X1) X0)) X2) X3
       grind)
    | (have r₁ := eq151 X0 X1 X2 (M.op (M.op X3 X1) X0)
       have r₂ := eq21 X0 X1 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact resolve eq151 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq167 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq99 (σ X1) (σ X0)
       grind)
    | exact superpose eq99 eq15
    | (have j1 := eq99 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq99 X1 (σ X0)
       grind)
    | exact superpose eq99 eq31
    | (have j1 := eq99 X1 (σ X0)
       grind)
    | exact resolve eq31 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq99 X1 (τ X0)
       grind)
    | exact superpose eq99 eq17
    | (have j1 := eq99 X1 (τ X0)
       grind)
    | exact resolve eq17 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177
    | exact resolve eq177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq824 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq775
    | (have j0 := eq775 X0 X1
       grind)
    | exact resolve eq775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq1139 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq1574 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1619 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1574 X0 X1
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq1574
    | (have j0 := eq1574 X0 X1
       grind)
    | exact resolve eq1574 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq1682 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1619 (τ X0) (τ X1)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq1619
    | (have j0 := eq1619 (τ X0) (τ X1)
       grind)
    | exact resolve eq1619 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq1894 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X1) X3) (σ X0)) ≠ (M.op (M.op (M.op X2 X1) X3) X1) ∨ (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (M.op X2 X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31 X0 (M.op (M.op X2 X1) X3)
       have i₂ := eq153 X2 X1 X3 (σ X0)
       grind)
    | exact superpose eq153 eq31
    | (have j1 := eq153 X2 X1 X3 (σ X0)
       grind)
    | exact resolve eq31 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq2769 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq80 X1 X0
       grind)
    | exact superpose eq80 eq25
    | (have j1 := eq80 X1 X0
       grind)
    | exact resolve eq25 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq3025 : ∀ X0 X1 : G, (τ (M.op X1 X1)) ≠ (M.op (τ X1) X0) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq167 X1 X0
       grind)
    | exact superpose eq167 eq18
    | (have j1 := eq167 X1 X0
       grind)
    | exact resolve eq18 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq167
  have eq6277 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2769 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2769
    | exact resolve eq2769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769
  have eq6339 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6277 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq6277
    | (have j0 := eq6277 X0 X1
       grind)
    | (have r₁ := eq6277 X0 X0
       have r₂ := eq44 X0
       grind)
    | exact resolve eq6277 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6277
  have eq6357 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6339 X0 X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq6339
    | (have j0 := eq6339 X0 X1
       grind)
    | exact resolve eq6339 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339
  have eq7123 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3025 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3025
    | exact resolve eq3025 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3025
  have eq7164 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (τ (σ (M.op X0 X0))) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7123 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq7123
    | (have j0 := eq7123 X0 X1
       grind)
    | exact resolve eq7123 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7123
  have eq7180 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7164 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq7164
    | (have j0 := eq7164 X0 X1
       grind)
    | (have r₁ := eq7164 X1 X1
       have r₂ := eq10 (M.op X1 X1)
       grind)
    | exact resolve eq7164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7164
  have eq7191 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7180 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7180
    | (have j0 := eq7180 X0 X1
       grind)
    | exact resolve eq7180 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7180
  have eq15841 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq1682 X0 X1
       grind)
    | exact superpose eq1682 eq13
    | (have j1 := eq1682 X0 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq1682 X0 X1
       grind)
    | exact resolve eq13 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15864 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (τ (k (τ X1) (τ X0))) = (τ (M.op (τ X1) (τ X0))) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6357 (τ X0) (τ X1)
       have i₂ := eq1682 X1 X0
       grind)
    | exact superpose eq1682 eq6357
    | (have j0 := eq6357 (τ X0) (τ X1)
       have j1 := eq1682 X1 X0
       grind)
    | exact resolve eq6357 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682 eq6357
  have eq15868 : ∀ X0 X1 : G, (τ X0) = (k (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq15841 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15841
  have eq15873 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (k (τ X1) (τ X0))) = (τ (M.op (τ X1) (τ X0))) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15864 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq15864
    | (have j0 := eq15864 X0 X1
       grind)
    | exact resolve eq15864 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15864
  have eq15880 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15868 X0 X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq15868
    | (have j0 := eq15868 X0 X1
       grind)
    | exact resolve eq15868 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15868
  have eq15938 : ∀ X0 X1 : G, (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) ∨ (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15873 X0 X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq15873
    | (have j0 := eq15873 X0 X1
       grind)
    | exact resolve eq15873 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq15873
  have eq15939 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq15938 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15938
  have eq15941 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15880 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq15880
    | (have j0 := eq15880 X0 X1
       grind)
    | exact resolve eq15880 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq15880
  have eq15974 : ∀ X0 X1 : G, (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq15941 X0 X1
       have j1 := eq15939 X0 X1
       grind)
    | (have r₁ := eq15941 X0 X1
       have r₂ := eq15939 X0 X1
       grind)
    | exact resolve eq15941 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15939 eq15941
  have eq16400 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (σ (τ (τ (k X0 X1)))) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (τ X0) (τ X1))
       have i₂ := eq15974 X1 X0
       grind)
    | exact superpose eq15974 eq11
    | (have j1 := eq15974 X1 X0
       grind)
    | exact resolve eq11 eq15974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15974
  have eq16540 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16400 X0 X1
       have i₂ := eq11 (τ (k X0 X1))
       grind)
    | exact superpose eq11 eq16400
    | (have j0 := eq16400 X0 X1
       grind)
    | exact resolve eq16400 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16400
  have eq16751 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op (τ X1) X0) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16540 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16540
    | exact resolve eq16540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16540
  have eq16921 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16751 X0 X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq16751
    | (have j0 := eq16751 X0 X1
       grind)
    | exact resolve eq16751 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16751
  have eq16963 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16921 X0 X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq16921
    | (have j0 := eq16921 X0 X1
       grind)
    | exact resolve eq16921 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16921
  have eq16993 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16963 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16963
    | exact resolve eq16963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17023 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq16963 X1 X0
       grind)
    | exact superpose eq16963 eq17
    | (have j1 := eq16963 X1 X0
       grind)
    | exact resolve eq17 eq16963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16963
  have eq17432 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq16993 (σ X0) X1
       grind)
    | exact superpose eq16993 eq31
    | (have j1 := eq16993 (σ X0) X1
       grind)
    | exact resolve eq31 eq16993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq17503 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1139
       have i₂ := eq16993 x y
       grind)
    | exact superpose eq16993 eq1139
    | (have j1 := eq16993 x y
       grind)
    | exact resolve eq1139 eq16993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16993
  have eq17505 : y = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq17503
  have eq17841 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1139
       have i₂ := eq17505
       grind)
    | exact superpose eq17505 eq1139
    | exact resolve eq1139 eq17505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139 eq17505
  have eq17860 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq17841
  have eq18439 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17023 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17023
    | exact resolve eq17023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17023
  have eq18608 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18439 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18439
    | (have j0 := eq18439 X0 X1
       grind)
    | exact resolve eq18439 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18439
  have eq19320 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) X0
       have i₂ := eq17432 X1 (σ X0)
       grind)
    | exact superpose eq17432 eq25
    | (have j1 := eq17432 X1 (σ X0)
       grind)
    | exact resolve eq25 eq17432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17432
  have eq19382 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19320 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq19320
    | (have j0 := eq19320 X0 X1
       grind)
    | exact resolve eq19320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19320
  have eq19420 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19382 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19382
    | (have j0 := eq19382 X0 X1
       grind)
    | exact resolve eq19382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19382
  have eq19430 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19420 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19420
    | (have j0 := eq19420 X0 X1
       grind)
    | exact resolve eq19420 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19420
  have eq20001 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq19430 X1 X0
       grind)
    | exact superpose eq19430 eq11
    | (have j1 := eq19430 X1 X0
       grind)
    | exact resolve eq11 eq19430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19430
  have eq20226 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20001 x y
       grind)
    | exact superpose eq20001 eq16
    | (have j1 := eq20001 x y
       grind)
    | exact resolve eq16 eq20001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20001
  have eq20385 : y = (k x y) := by
    first
    | (have j1 := eq18608 x y
       grind)
    | (have r₁ := eq20226
       have r₂ := eq18608 x y
       grind)
    | exact resolve eq20226 eq18608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18608 eq20226
  have eq20888 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq99 y x
       have i₂ := eq20385
       grind)
    | exact superpose eq20385 eq99
    | (have j0 := eq99 y x
       grind)
    | exact resolve eq99 eq20385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq20889 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq824 x y
       have i₂ := eq20385
       grind)
    | exact superpose eq20385 eq824
    | (have j0 := eq824 x y
       grind)
    | exact resolve eq824 eq20385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq39861 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1894 X0 (σ X0) X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq39862 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39861 X0 X1 X2
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq39861
    | exact resolve eq39861 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39861
  have eq39919 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (τ (M.op (M.op X1 (σ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39862 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq39862
    | exact resolve eq39862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39862
  have eq40232 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ (M.op (M.op X1 (σ (τ X0))) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (τ (M.op (M.op X1 (σ (τ X0))) X2))
       have i₂ := eq39919 (τ X0) X1 X2
       grind)
    | exact superpose eq39919 eq17
    | exact resolve eq17 eq39919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq40343 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (M.op (M.op X1 (σ (τ X0))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40232 X0 X1 X2
       have i₂ := eq11 (M.op (M.op X1 (σ (τ X0))) X2)
       grind)
    | exact superpose eq11 eq40232
    | exact resolve eq40232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40232
  have eq40452 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40343 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40343
    | exact resolve eq40343 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40343
  have eq40530 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40452 X0 X1 X2
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq40452
    | exact resolve eq40452 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq40452
  have eq40686 : ∀ X0 : G, (M.op x x) = (k x (M.op y X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq40530 x y X0
       have i₂ := eq20889
       grind)
    | exact superpose eq20889 eq40530
    | exact resolve eq40530 eq20889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40530
  have eq55023 : (k x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40686 x
       have i₂ := eq20889
       grind)
    | exact superpose eq20889 eq40686
    | exact resolve eq40686 eq20889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20889 eq40686
  have eq55106 : (k x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq55023
  have eq55128 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq55106
       have i₂ := eq20385
       grind)
    | exact superpose eq20385 eq55106
    | exact resolve eq55106 eq20385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55106
  have eq55212 : y ≠ y ∨ (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq7191 x x
       have i₂ := eq55128
       grind)
    | exact superpose eq55128 eq7191
    | exact resolve eq7191 eq55128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55128
  have eq55218 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq55212
  have eq55226 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq55218
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq55218
    | exact resolve eq55218 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55218
  have eq56227 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17860
       have i₂ := eq55226
       grind)
    | exact superpose eq55226 eq17860
    | (have r₁ := eq17860
       have r₂ := eq55226
       grind)
    | exact resolve eq17860 eq55226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55226
  have eq56339 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq56227
  have eq58733 : ∀ X0 : G, (M.op x x) = (k x (τ (M.op (σ y) X0))) ∨ (σ y) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq39919 x (σ y) X0
       have i₂ := eq56339
       grind)
    | exact superpose eq56339 eq39919
    | exact resolve eq39919 eq56339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39919
  have eq270389 : (M.op x x) = (k x (τ (σ y))) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq58733 (σ x)
       have i₂ := eq56339
       grind)
    | exact superpose eq56339 eq58733
    | exact resolve eq58733 eq56339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56339 eq58733
  have eq270634 : (M.op x x) = (k x (τ (σ y))) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq270389
  have eq270716 : (k x y) = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq270634
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq270634
    | exact resolve eq270634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270634
  have eq270774 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq270716
       have i₂ := eq20385
       grind)
    | exact superpose eq20385 eq270716
    | exact resolve eq270716 eq20385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20385 eq270716
  have eq270914 : y ≠ y ∨ (σ y) = (σ (k x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7191 x x
       have i₂ := eq270774
       grind)
    | exact superpose eq270774 eq7191
    | exact resolve eq7191 eq270774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7191 eq270774
  have eq270934 : (σ y) = (σ (k x x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq270914
  have eq270947 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq270934
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq270934
    | exact resolve eq270934 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq270934
  have eq270948 : (σ y) = (σ (M.op x x)) := by grind
  clear eq270947
  have eq271788 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 x X0 X1
       have i₂ := eq270948
       grind)
    | exact superpose eq270948 eq139
    | exact resolve eq139 eq270948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq271833 : (τ (σ y)) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq270948
       grind)
    | exact superpose eq270948 eq10
    | exact resolve eq10 eq270948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272176 : y = (M.op x x) := by
    first
    | (have i₁ := eq271833
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq271833
    | exact resolve eq271833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271833
  have eq272274 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 x X0 x
       have i₂ := eq272176
       grind)
    | exact superpose eq272176 eq21
    | exact resolve eq21 eq272176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275071 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq272274 X0 x
       have i₂ := eq20888
       grind)
    | exact superpose eq20888 eq272274
    | exact resolve eq272274 eq20888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20888
  have eq298203 : y ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq275071 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275071
  have eq298210 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq298203
       have r₂ := eq272176
       grind)
    | exact resolve eq298203 eq272176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298203
  have eq298219 : y = (M.op x y) := by
    first
    | (have i₁ := eq298210
       have i₂ := eq272176
       grind)
    | exact superpose eq272176 eq298210
    | exact resolve eq298210 eq272176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272176 eq298210
  have eq299313 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq17860
       have i₂ := eq298219
       grind)
    | exact superpose eq298219 eq17860
    | exact resolve eq17860 eq298219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17860
  have eq299327 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 y X0 x
       have i₂ := eq298219
       grind)
    | exact superpose eq298219 eq21
    | exact resolve eq21 eq298219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq298219
  have eq299393 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq299313
  have eq299399 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq299327 X0 x
       have i₂ := eq272274 X0 x
       grind)
    | exact superpose eq272274 eq299327
    | exact resolve eq299327 eq272274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272274 eq299327
  have eq301066 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq271788 X0 (σ x)
       have i₂ := eq299393
       grind)
    | exact superpose eq299393 eq271788
    | exact resolve eq271788 eq299393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271788 eq299393
  have eq305095 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq301066 (σ x)
       grind)
    | exact superpose eq301066 eq16
    | exact resolve eq16 eq301066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301066
  have eq305329 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq305095
       have i₂ := eq42 x
       grind)
    | exact superpose eq42 eq305095
    | exact resolve eq305095 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq305095
  have eq305594 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq305329
       have i₂ := eq270948
       grind)
    | exact superpose eq270948 eq305329
    | exact resolve eq305329 eq270948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305329
  have eq305740 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq305594
       have i₂ := eq299399 x
       grind)
    | exact superpose eq299399 eq305594
    | exact resolve eq305594 eq299399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299399 eq305594
  have eq305814 : False := by grind
  exact eq305814

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq39 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
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
  clear eq37
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq40
    | exact resolve eq40 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq99 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq115 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 (σ X0) X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq21
    | exact resolve eq21 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op (M.op X0 X1) X2) X1) ∨ (M.op X3 (M.op (M.op X0 X1) X2)) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op (M.op X0 X1) X2)
       have i₂ := eq21 X2 X1 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X3 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq21 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq21 X0 X1 X1 X3
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (k X3 (M.op (M.op X0 X1) X2)) ∨ (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op (M.op X0 X1) X2) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq151 X0 X1 X2 X3
       have i₂ := eq21 X2 X1 X3 X0
       grind)
    | exact superpose eq21 eq151
    | (have j0 := eq151 X0 X1 X2 X3
       grind)
    | (have r₁ := eq151 X0 (M.op (M.op X3 X1) X0) X2 X1
       have r₂ := eq21 X0 X1 (M.op (M.op X0 (M.op (M.op X3 X1) X0)) X2) X3
       grind)
    | (have r₁ := eq151 X0 X1 X2 (M.op (M.op X3 X1) X0)
       have r₂ := eq21 X0 X1 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact resolve eq151 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq99 (σ X1) (σ X0)
       grind)
    | exact superpose eq99 eq15
    | (have j1 := eq99 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq99 X1 (σ X0)
       grind)
    | exact superpose eq99 eq31
    | (have j1 := eq99 X1 (σ X0)
       grind)
    | exact resolve eq31 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq99 X1 (τ X0)
       grind)
    | exact superpose eq99 eq17
    | (have j1 := eq99 X1 (τ X0)
       grind)
    | exact resolve eq17 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq775 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177
    | exact resolve eq177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq824 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq775
    | (have j0 := eq775 X0 X1
       grind)
    | exact resolve eq775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq1139 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq1574 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1619 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1574 X0 X1
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq1574
    | (have j0 := eq1574 X0 X1
       grind)
    | exact resolve eq1574 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq1682 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1619 (τ X0) (τ X1)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq1619
    | (have j0 := eq1619 (τ X0) (τ X1)
       grind)
    | exact resolve eq1619 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq1894 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X1) X3) (σ X0)) ≠ (M.op (M.op (M.op X2 X1) X3) X1) ∨ (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (M.op X2 X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31 X0 (M.op (M.op X2 X1) X3)
       have i₂ := eq153 X2 X1 X3 (σ X0)
       grind)
    | exact superpose eq153 eq31
    | (have j1 := eq153 X2 X1 X3 (σ X0)
       grind)
    | exact resolve eq31 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq2769 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq80 X1 X0
       grind)
    | exact superpose eq80 eq25
    | (have j1 := eq80 X1 X0
       grind)
    | exact resolve eq25 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq6277 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2769 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2769
    | exact resolve eq2769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769
  have eq6339 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6277 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq6277
    | (have j0 := eq6277 X0 X1
       grind)
    | (have r₁ := eq6277 X0 X0
       have r₂ := eq44 X0
       grind)
    | exact resolve eq6277 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq6277
  have eq6357 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6339 X0 X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq6339
    | (have j0 := eq6339 X0 X1
       grind)
    | exact resolve eq6339 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339
  have eq15841 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq1682 X0 X1
       grind)
    | exact superpose eq1682 eq13
    | (have j0 := eq13 (τ X1) (τ X0)
       have j1 := eq1682 X0 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq1682 X0 X1
       grind)
    | exact resolve eq13 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15864 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (τ (k (τ X1) (τ X0))) = (τ (M.op (τ X1) (τ X0))) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6357 (τ X0) (τ X1)
       have i₂ := eq1682 X1 X0
       grind)
    | exact superpose eq1682 eq6357
    | (have j0 := eq6357 (τ X0) (τ X1)
       have j1 := eq1682 X1 X0
       grind)
    | exact resolve eq6357 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682 eq6357
  have eq15868 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq15841 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15841
  have eq15873 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (k (τ X1) (τ X0))) = (τ (M.op (τ X1) (τ X0))) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15864 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq15864
    | (have j0 := eq15864 X0 X1
       grind)
    | exact resolve eq15864 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15864
  have eq15880 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15868 X0 X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq15868
    | (have j0 := eq15868 X0 X1
       grind)
    | exact resolve eq15868 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15868
  have eq15938 : ∀ X0 X1 : G, (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) ∨ (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15873 X0 X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq15873
    | (have j0 := eq15873 X0 X1
       grind)
    | exact resolve eq15873 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq15873
  have eq15939 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq15938 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15938
  have eq15941 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X1) = (τ (k X1 X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15880 X0 X1
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq15880
    | (have j0 := eq15880 X0 X1
       grind)
    | exact resolve eq15880 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq15880
  have eq15974 : ∀ X0 X1 : G, (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq15941 X0 X1
       have j1 := eq15939 X0 X1
       grind)
    | (have r₁ := eq15941 X0 X1
       have r₂ := eq15939 X0 X1
       grind)
    | exact resolve eq15941 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15939 eq15941
  have eq16400 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (σ (τ (τ (k X0 X1)))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (τ X0) (τ X1))
       have i₂ := eq15974 X1 X0
       grind)
    | exact superpose eq15974 eq11
    | (have j1 := eq15974 X1 X0
       grind)
    | exact resolve eq11 eq15974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15974
  have eq16540 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16400 X0 X1
       have i₂ := eq11 (τ (k X0 X1))
       grind)
    | exact superpose eq11 eq16400
    | (have j0 := eq16400 X0 X1
       grind)
    | exact resolve eq16400 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16400
  have eq16733 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16540 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16540
    | exact resolve eq16540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16540
  have eq16929 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16733 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq16733
    | (have j0 := eq16733 X0 X1
       grind)
    | exact resolve eq16733 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16733
  have eq16970 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16929 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq16929
    | (have j0 := eq16929 X0 X1
       grind)
    | exact resolve eq16929 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16929
  have eq16994 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16970 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16970
    | exact resolve eq16970 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17023 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq16970 X0 X1
       grind)
    | exact superpose eq16970 eq18
    | (have j1 := eq16970 X0 X1
       grind)
    | exact resolve eq18 eq16970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16970
  have eq17389 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq16994 (σ X1) X0
       grind)
    | exact superpose eq16994 eq25
    | (have j1 := eq16994 (σ X1) X0
       grind)
    | exact resolve eq25 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq17501 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1139
       have i₂ := eq16994 y x
       grind)
    | exact superpose eq16994 eq1139
    | (have j1 := eq16994 y x
       grind)
    | exact resolve eq1139 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17502 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq16994 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16994
  have eq17503 : x = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq17501
  have eq17521 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op (M.op X2 X1) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17502 X0 (M.op (M.op X2 X1) X3)
       have i₂ := eq21 X3 X1 X0 X2
       grind)
    | exact superpose eq21 eq17502
    | (have j0 := eq17502 X0 X1
       grind)
    | exact resolve eq17502 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17502
  have eq17829 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1139
       have i₂ := eq17503
       grind)
    | exact superpose eq17503 eq1139
    | exact resolve eq1139 eq17503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17503
  have eq17848 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq17829
  have eq18961 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17023 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17023
    | exact resolve eq17023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17023
  have eq19107 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18961 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18961
    | (have j0 := eq18961 X0 X1
       grind)
    | exact resolve eq18961 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18961
  have eq19642 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X1)
       have i₂ := eq17389 (σ X0) X1
       grind)
    | exact superpose eq17389 eq31
    | (have j1 := eq17389 (σ X0) X1
       grind)
    | exact resolve eq31 eq17389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17389
  have eq19714 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19642 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq19642
    | (have j0 := eq19642 X0 X1
       grind)
    | exact resolve eq19642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19642
  have eq19747 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19714 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19714
    | (have j0 := eq19714 X0 X1
       grind)
    | exact resolve eq19714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19714
  have eq19757 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19747 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19747
    | (have j0 := eq19747 X0 X1
       grind)
    | exact resolve eq19747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19747
  have eq20513 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq19757 X0 X1
       grind)
    | exact superpose eq19757 eq11
    | (have j1 := eq19757 X0 X1
       grind)
    | exact resolve eq11 eq19757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21204 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20513 x y
       grind)
    | exact superpose eq20513 eq16
    | (have j1 := eq20513 x y
       grind)
    | exact resolve eq16 eq20513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20513
  have eq21364 : x = (k x y) := by
    first
    | (have j1 := eq19107 y x
       grind)
    | (have r₁ := eq21204
       have r₂ := eq19107 y x
       grind)
    | exact resolve eq21204 eq19107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19107 eq21204
  have eq21430 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq824 x y
       have i₂ := eq21364
       grind)
    | exact superpose eq21364 eq824
    | (have j0 := eq824 x y
       grind)
    | exact resolve eq824 eq21364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq22416 : ∀ X0 X1 : G, y ≠ y ∨ y = (k y (M.op (M.op X0 x) X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq17521 y x X0 X1
       have i₂ := eq21430
       grind)
    | exact superpose eq21430 eq17521
    | (have j0 := eq17521 y x X0 X1
       grind)
    | (have r₁ := eq17521 y x x x
       have r₂ := eq21430
       grind)
    | exact resolve eq17521 eq21430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17521
  have eq22417 : ∀ X0 X1 : G, y = (k y (M.op (M.op X0 x) X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq22416 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22416
  have eq34877 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1894 X0 (σ X0) X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq34878 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34877 X0 X1 X2
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq34877
    | exact resolve eq34877 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34877
  have eq34935 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (τ (M.op (M.op X1 (σ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34878 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq34878
    | exact resolve eq34878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34878
  have eq48988 : ∀ X0 : G, y = (k y (M.op y X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq22417 y X0
       have i₂ := eq21430
       grind)
    | exact superpose eq21430 eq22417
    | exact resolve eq22417 eq21430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22417
  have eq49065 : ∀ X0 : G, y = (k y (M.op y X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq48988 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48988
  have eq49496 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49065 x
       have i₂ := eq21430
       grind)
    | exact superpose eq21430 eq49065
    | exact resolve eq49065 eq21430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21430 eq49065
  have eq49570 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq49496
  have eq49592 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq49570
       have i₂ := eq35 y
       grind)
    | exact superpose eq35 eq49570
    | exact resolve eq49570 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq49570
  have eq49598 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (M.op X0 y) = (k X0 y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq49592
       grind)
    | exact superpose eq49592 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq49592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49592
  have eq49711 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq49598 X0
       have j1 := eq99 y X0
       grind)
    | (have r₁ := eq49598 x
       have r₂ := eq99 y x
       grind)
    | exact resolve eq49598 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49598
  have eq52279 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1139
       have i₂ := eq49711 x
       grind)
    | exact superpose eq49711 eq1139
    | exact resolve eq1139 eq49711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139 eq49711
  have eq52280 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq52279
  have eq52281 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq52280
       have r₂ := eq17848
       grind)
    | exact resolve eq52280 eq17848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17848 eq52280
  have eq52693 : (k y x) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq19757 y x
       have i₂ := eq52281
       grind)
    | exact superpose eq52281 eq19757
    | (have j0 := eq19757 y x
       grind)
    | exact resolve eq19757 eq52281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19757
  have eq52711 : ∀ X0 : G, (M.op x x) = (k x (τ (M.op (σ y) X0))) := by
    intro X0
    first
    | (have i₁ := eq34935 x (σ y) X0
       have i₂ := eq52281
       grind)
    | exact superpose eq52281 eq34935
    | exact resolve eq34935 eq52281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34935
  have eq52718 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (σ x) X0 (σ y)
       have i₂ := eq52281
       grind)
    | exact superpose eq52281 eq21
    | exact resolve eq21 eq52281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52779 : y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq52693
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq52693
    | exact resolve eq52693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52693
  have eq52780 : y = (k y x) := by grind
  clear eq52779
  have eq53478 : (M.op x x) = (k x (τ (σ y))) := by
    first
    | (have i₁ := eq52711 (σ x)
       have i₂ := eq52281
       grind)
    | exact superpose eq52281 eq52711
    | exact resolve eq52711 eq52281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52281 eq52711
  have eq53634 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq53478
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq53478
    | exact resolve eq53478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53478
  have eq53668 : x = (M.op x x) := by
    first
    | (have i₁ := eq53634
       have i₂ := eq21364
       grind)
    | exact superpose eq21364 eq53634
    | exact resolve eq53634 eq21364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21364 eq53634
  have eq54301 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq53668
       grind)
    | exact superpose eq53668 eq12
    | (have j0 := eq12 X0 x
       grind)
    | exact resolve eq12 eq53668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54419 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq54301 X0
       have j1 := eq99 x X0
       grind)
    | (have r₁ := eq54301 x
       have r₂ := eq99 x x
       grind)
    | exact resolve eq54301 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq54301
  have eq55017 : y = (M.op y x) := by
    first
    | (have i₁ := eq52780
       have i₂ := eq54419 y
       grind)
    | exact superpose eq54419 eq52780
    | exact resolve eq52780 eq54419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52780 eq54419
  have eq55036 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 x X0 y
       have i₂ := eq55017
       grind)
    | exact superpose eq55017 eq21
    | exact resolve eq21 eq55017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq58924 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq55036 X0 x
       have i₂ := eq55017
       grind)
    | exact superpose eq55017 eq55036
    | exact resolve eq55036 eq55017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55036
  have eq59746 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 y X0 X1
       have i₂ := eq58924 y
       grind)
    | exact superpose eq58924 eq139
    | exact resolve eq139 eq58924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq60050 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq59746 X0 X1
       have i₂ := eq55017
       grind)
    | exact superpose eq55017 eq59746
    | exact resolve eq59746 eq55017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55017 eq59746
  have eq60096 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq60050 X0 x
       have i₂ := eq52718 X0 x
       grind)
    | exact superpose eq52718 eq60050
    | exact resolve eq60050 eq52718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52718 eq60050
  have eq62661 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60096 (σ x)
       grind)
    | exact superpose eq60096 eq16
    | exact resolve eq16 eq60096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60096
  have eq62750 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq62661
       have i₂ := eq42 x
       grind)
    | exact superpose eq42 eq62661
    | exact resolve eq62661 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq62661
  have eq62895 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq62750
       have i₂ := eq53668
       grind)
    | exact superpose eq53668 eq62750
    | exact resolve eq62750 eq53668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62750
  have eq62975 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq62895
       have i₂ := eq58924 x
       grind)
    | exact superpose eq58924 eq62895
    | exact resolve eq62895 eq58924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58924 eq62895
  have eq63020 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq62975
       have i₂ := eq53668
       grind)
    | exact superpose eq53668 eq62975
    | exact resolve eq62975 eq53668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53668 eq62975
  have eq63021 : False := by grind
  exact eq63021
