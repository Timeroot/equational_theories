import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_y_pxx_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
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
  clear eq25 eq36
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
  have eq51 : x ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
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
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op (M.op X0 X1) X2) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq117 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X3) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1 X2 X3
    grind
  have eq118 : ∀ X0 X3 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X3) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq117 X0 x x X3
       have i₂ := eq14 X0 X0 x x
       grind)
    | exact superpose eq14 eq117
    | (have j0 := eq117 X0 x x X3
       grind)
    | exact resolve eq117 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq231 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1313 : ∀ X2 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x x) X2) = X2 := by
    intro X2
    first
    | exact superpose eq61 eq67
    | (have j0 := eq67 x y (M.op x y) x
       grind)
    | exact resolve eq67 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq2149 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2151 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq8368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8368
    | exact resolve eq8368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8368
  have eq8380 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8369
       have r₂ := eq28
       grind)
    | exact resolve eq8369 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8369
  have eq8382 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8380
    | exact resolve eq8380 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8380
  have eq8390 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq8382 eq63
    | exact resolve eq63 eq8382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8407 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq8382 eq118
    | exact resolve eq118 eq8382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8382
  have eq8414 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq27 eq8407
    | (have j0 := eq8407 X0
       grind)
    | exact resolve eq8407 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8407
  have eq8415 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq8414 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8414
  have eq8649 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8390
    | (have j0 := eq8390 (σ y)
       grind)
    | exact resolve eq8390 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8390
  have eq9030 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq8415 eq90
    | exact resolve eq90 eq8415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8415
  have eq9067 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq9030 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9030
  have eq9108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9067 eq8649
    | (have j1 := eq9067 (σ y)
       grind)
    | exact resolve eq8649 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8649 eq9067
  have eq9153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq9108
  have eq9177 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9153
       have r₂ := eq28
       grind)
    | exact resolve eq9153 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9153
  have eq9191 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq63 y y x
       have i₂ := eq9177
       grind)
    | exact superpose eq9177 eq63
    | exact resolve eq63 eq9177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9208 : ∀ X0 : G, (k x y) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq118 y x
       have i₂ := eq9177
       grind)
    | exact superpose eq9177 eq118
    | exact resolve eq118 eq9177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9177
  have eq9215 : ∀ X0 : G, x = (M.op x y) ∨ (k x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9208 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9208
    | (have j0 := eq9208 X0
       grind)
    | exact resolve eq9208 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9208
  have eq9216 : ∀ X0 : G, (k x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq9215 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9215
  have eq10069 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9191 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9191
    | (have j0 := eq9191 y
       grind)
    | exact resolve eq9191 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10152 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9191 X0
       have i₂ := eq10069
       grind)
    | exact superpose eq10069 eq9191
    | exact resolve eq9191 eq10069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9191 eq10069
  have eq10185 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10152
  have eq10687 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10185 x
       have i₂ := eq9216 x
       grind)
    | exact superpose eq9216 eq10185
    | (have j1 := eq9216 y
       grind)
    | exact resolve eq10185 eq9216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9216 eq10185
  have eq10707 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10687
  have eq10736 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq10707
       grind)
    | exact superpose eq10707 eq45
    | exact resolve eq45 eq10707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq10707
  have eq10753 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10736
    | exact resolve eq10736 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10736
  have eq10767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10753 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq10753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10767
    | exact resolve eq10767 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10767
  have eq10781 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10770
       have r₂ := eq28
       grind)
    | exact resolve eq10770 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10770
  have eq10783 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10781
    | exact resolve eq10781 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10781
  have eq10784 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10783
  have eq10793 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10784 eq63
    | exact resolve eq63 eq10784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10812 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10784 eq118
    | exact resolve eq118 eq10784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10784
  have eq10819 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq10812
    | (have j0 := eq10812 X0
       grind)
    | exact resolve eq10812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10812
  have eq10820 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10819
  have eq12552 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq10793
    | (have j0 := eq10793 (σ y)
       grind)
    | exact resolve eq10793 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10793
  have eq13193 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10820 eq10753
    | exact resolve eq10753 eq10820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10753 eq10820
  have eq13245 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13193
  have eq13309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13245 eq12552
    | (have j1 := eq13245 (σ y)
       grind)
    | exact resolve eq12552 eq13245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12552 eq13245
  have eq13373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13309
  have eq13411 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13373
       have r₂ := eq28
       grind)
    | exact resolve eq13373 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13373
  have eq13426 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13411 eq52
    | (have r₁ := eq52
       have r₂ := eq13411
       grind)
    | exact resolve eq52 eq13411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq13427 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13411 eq62
    | exact resolve eq62 eq13411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq13433 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13426
  have eq13442 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13433 eq56
    | exact resolve eq56 eq13433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq13443 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13433 eq90
    | exact resolve eq90 eq13433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq13433
  have eq13459 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13443
  have eq13471 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq13442
    | exact resolve eq13442 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13442
  have eq13476 : y = (k x y) := by
    first
    | (have r₁ := eq13471
       have r₂ := eq51
       grind)
    | exact resolve eq13471 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq13471
  have eq13749 : ∀ X0 : G, (k x y) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq118 y x
       have i₂ := eq13459
       grind)
    | exact superpose eq13459 eq118
    | exact resolve eq118 eq13459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13459
  have eq13756 : ∀ X0 : G, y = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13749 X0
       have i₂ := eq13476
       grind)
    | exact superpose eq13476 eq13749
    | exact resolve eq13749 eq13476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13749
  have eq13771 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13756 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13756
    | (have j0 := eq13756 X0
       grind)
    | exact resolve eq13756 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13756
  have eq13772 : ∀ X0 : G, y = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq13771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13771
  have eq14014 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13772 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13772
    | (have j0 := eq13772 y
       grind)
    | exact resolve eq13772 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13772
  have eq14119 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14014 eq30
    | exact resolve eq30 eq14014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14014
  have eq14232 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq14119
    | exact resolve eq14119 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14119
  have eq14233 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq14232
  have eq14311 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq17633 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq13427
    | (have j0 := eq13427 (σ y) X0
       grind)
    | exact resolve eq13427 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13427
  have eq17812 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13411 eq17633
    | exact resolve eq17633 eq13411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17633
  have eq17874 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17812
  have eq18192 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17874
    | (have j0 := eq17874 (σ y)
       grind)
    | exact resolve eq17874 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17874
  have eq18442 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18192 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18192
       grind)
    | exact resolve eq13 eq18192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18192
  have eq18531 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18442
       have r₂ := eq13411
       grind)
    | exact resolve eq18442 eq13411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13411 eq18442
  have eq19033 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18531 eq50
    | exact resolve eq50 eq18531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq18531
  have eq19059 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19033
    | exact resolve eq19033 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19033
  have eq20153 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq19059
       grind)
    | exact superpose eq19059 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq19059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19059
  have eq20154 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq20153
  have eq21240 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58 x x X2 X3 x x
       have i₂ := eq20154
       grind)
    | exact superpose eq20154 eq58
    | exact resolve eq58 eq20154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq21304 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) := by
    intro X3
    first
    | (have i₁ := eq21240 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq21240
    | exact resolve eq21240 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21240
  have eq21312 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21304 x
       have i₂ := eq231 x
       grind)
    | exact superpose eq231 eq21304
    | exact resolve eq21304 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq21304
  have eq21336 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14233 eq21312
    | exact resolve eq21312 eq14233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14233 eq21312
  have eq21417 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21336
       have r₂ := eq14311
       grind)
    | exact resolve eq21336 eq14311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21336
  have eq21465 : ∀ X0 : G, (k x y) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq118 y x
       have i₂ := eq21417
       grind)
    | exact superpose eq21417 eq118
    | exact resolve eq118 eq21417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq21417
  have eq21474 : ∀ X0 : G, y = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21465 X0
       have i₂ := eq13476
       grind)
    | exact superpose eq13476 eq21465
    | exact resolve eq21465 eq13476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13476 eq21465
  have eq21490 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21474 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21474
    | (have j0 := eq21474 X0
       grind)
    | exact resolve eq21474 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21474
  have eq21491 : ∀ X0 : G, y = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21490 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21490
  have eq21527 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20154
       have i₂ := eq21491 x
       grind)
    | exact superpose eq21491 eq20154
    | exact resolve eq20154 eq21491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20154 eq21491
  have eq21584 : x = y ∨ x = (M.op x y) := by grind
  clear eq21527
  have eq21617 : x = (M.op x y) := by
    first
    | (have r₁ := eq21584
       have r₂ := eq14311
       grind)
    | exact resolve eq21584 eq14311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14311 eq21584
  have eq21632 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21617 eq21
    | exact resolve eq21 eq21617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21635 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq21617 eq61
    | exact resolve eq61 eq21617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq21687 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq21617 eq1313
    | (have j0 := eq1313 X0
       grind)
    | exact resolve eq1313 eq21617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq21689 : ∀ X0 : G, (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq21687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21687
  have eq21741 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21632
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21632
    | exact resolve eq21632 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21632
  have eq21756 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21741 eq27
    | exact resolve eq27 eq21741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq24186 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq21635 y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21635
    | (have j0 := eq21635 y X0
       grind)
    | exact resolve eq21635 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21635
  have eq24343 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq21617 eq24186
    | exact resolve eq24186 eq21617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24186
  have eq24464 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq24343 y
       grind)
    | exact superpose eq24343 eq19
    | (have j1 := eq24343 y
       grind)
    | exact resolve eq19 eq24343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24343
  have eq24503 : x = (M.op x x) := by
    first
    | exact superpose eq21617 eq24464
    | exact resolve eq24464 eq21617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21617 eq24464
  have eq24589 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21689 X0
       have i₂ := eq24503
       grind)
    | exact superpose eq24503 eq21689
    | exact resolve eq21689 eq24503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21689 eq24503
  have eq25024 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2151 x
       have i₂ := eq24589 x
       grind)
    | exact superpose eq24589 eq2151
    | (have j0 := eq2151 x
       grind)
    | exact resolve eq2151 eq24589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151 eq24589
  have eq25081 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25024
  have eq25129 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25081
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25081
    | exact resolve eq25081 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25081
  have eq25165 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21741 eq25129
    | exact resolve eq25129 eq21741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21741 eq25129
  have eq25371 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq25165 eq63
    | exact resolve eq63 eq25165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq25420 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq25165 eq25371
    | exact resolve eq25371 eq25165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25165 eq25371
  have eq25451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25420 eq21756
    | exact resolve eq21756 eq25420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21756 eq25420
  have eq25522 : False := by grind
  exact eq25522

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_pxy_x_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq88 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq213 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq3938 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq88 (σ X1) X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3955 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq88 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq3956 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955
  have eq3957 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3938 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3938
  have eq3958 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3957 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3957
  have eq3960 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3956 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3956
    | (have j0 := eq3956 X0
       grind)
    | exact resolve eq3956 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq3992 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq3960 X0
       grind)
    | exact superpose eq3960 eq46
    | (have j1 := eq3960 X0
       grind)
    | exact resolve eq46 eq3960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq3960
  have eq4004 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3992 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3992
    | (have j0 := eq3992 X0
       grind)
    | exact resolve eq3992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq4005 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4004 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004
  have eq4007 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4005 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4005
    | exact resolve eq4005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4029 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4005 X0
       grind)
    | exact superpose eq4005 eq11
    | exact resolve eq11 eq4005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005
  have eq4089 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4007 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq4007
    | exact resolve eq4007 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4007
  have eq4315 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4089 X0
       grind)
    | exact superpose eq4089 eq11
    | exact resolve eq11 eq4089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4425 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4315 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4315
    | exact resolve eq4315 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq4486 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq4425 (τ X0)
       grind)
    | exact superpose eq4425 eq34
    | exact resolve eq34 eq4425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4540 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4486 X0
       have i₂ := eq4089 X0
       grind)
    | exact superpose eq4089 eq4486
    | exact resolve eq4486 eq4089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089 eq4486
  have eq5052 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq5069 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5052 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq5052
    | exact resolve eq5052 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5052
  have eq5097 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5069 X0
       have i₂ := eq4425 X0
       grind)
    | exact superpose eq4425 eq5069
    | exact resolve eq5069 eq4425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069
  have eq5107 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5097
  have eq23674 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq3958 (σ X0) X1
       grind)
    | exact superpose eq3958 eq30
    | (have j1 := eq3958 (σ X0) X1
       grind)
    | exact resolve eq30 eq3958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3958
  have eq23763 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23674 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq23674
    | (have j0 := eq23674 X0 X1
       grind)
    | exact resolve eq23674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23674
  have eq23837 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23763 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23763
    | (have j0 := eq23763 X0 X1
       grind)
    | exact resolve eq23763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23763
  have eq23904 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23837 X0 X1
       have i₂ := eq4029 X0
       grind)
    | exact superpose eq4029 eq23837
    | (have j0 := eq23837 X0 X1
       grind)
    | exact resolve eq23837 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23837
  have eq23948 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23904 X0 X1
       have i₂ := eq4425 X0
       grind)
    | exact superpose eq4425 eq23904
    | (have j0 := eq23904 X0 X1
       grind)
    | exact resolve eq23904 eq4425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23904
  have eq23985 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23948 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23948
    | (have j0 := eq23948 X0 X1
       grind)
    | exact resolve eq23948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23948
  have eq27199 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23985 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23985
    | (have j0 := eq23985 X1 (τ X0)
       grind)
    | exact resolve eq23985 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27248 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq23985 X0 X1
       grind)
    | exact superpose eq23985 eq11
    | (have j1 := eq23985 X0 X1
       grind)
    | exact resolve eq11 eq23985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23985
  have eq27672 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27199 X0 (τ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq27199
    | (have j0 := eq27199 X1 (τ X0)
       grind)
    | exact resolve eq27199 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq27199
  have eq27854 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27672 X0 X1
       have i₂ := eq4540 X0
       grind)
    | exact superpose eq4540 eq27672
    | (have j0 := eq27672 X0 X1
       grind)
    | exact resolve eq27672 eq4540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4540 eq27672
  have eq27936 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27854 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq27854
    | (have j0 := eq27854 X0 X1
       grind)
    | exact resolve eq27854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27854
  have eq28007 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27936 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27936
    | (have j0 := eq27936 X0 X1
       grind)
    | exact resolve eq27936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27936
  have eq28447 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq28007 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28007
  have eq30488 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27248 x y
       grind)
    | exact superpose eq27248 eq16
    | (have j1 := eq27248 x y
       grind)
    | exact resolve eq16 eq27248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27248
  have eq30929 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30488
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq30488
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq30488 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30488
  have eq30932 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq30929
  have eq30933 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq30932
  have eq31119 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq28447 x y
       have i₂ := eq30933
       grind)
    | exact superpose eq30933 eq28447
    | (have j0 := eq28447 x y
       grind)
    | exact resolve eq28447 eq30933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28447
  have eq31120 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq31119
  have eq31121 : y = (M.op x x) ∨ (τ x) = (τ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq31120
  have eq31731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5107 x
       have i₂ := eq31121
       grind)
    | exact superpose eq31121 eq5107
    | exact resolve eq5107 eq31121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31121
  have eq31756 : (σ y) = (σ (M.op x x)) ∨ (τ x) = (τ (k x y)) := by
    first
    | (have r₁ := eq31731
       have r₂ := eq16
       grind)
    | exact resolve eq31731 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31731
  have eq31774 : (M.op x x) = (τ (σ y)) ∨ (τ x) = (τ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq31756
       grind)
    | exact superpose eq31756 eq10
    | exact resolve eq10 eq31756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31756
  have eq31903 : y = (M.op x x) ∨ (τ x) = (τ (k x y)) := by
    first
    | (have i₁ := eq31774
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq31774
    | exact resolve eq31774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31774
  have eq32339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k x y)) := by
    first
    | (have i₁ := eq5107 x
       have i₂ := eq31903
       grind)
    | exact superpose eq31903 eq5107
    | exact resolve eq5107 eq31903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31903
  have eq32364 : (τ x) = (τ (k x y)) := by
    first
    | (have r₁ := eq32339
       have r₂ := eq16
       grind)
    | exact resolve eq32339 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32339
  have eq32380 : (k x y) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq32364
       grind)
    | exact superpose eq32364 eq11
    | exact resolve eq11 eq32364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32364
  have eq32553 : x = (k x y) := by
    first
    | (have i₁ := eq32380
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq32380
    | exact resolve eq32380 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32380
  have eq32988 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq213 x y
       have i₂ := eq32553
       grind)
    | exact superpose eq32553 eq213
    | (have j0 := eq213 x y
       grind)
    | exact resolve eq213 eq32553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq32553
  have eq32997 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq32988
  have eq33002 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32997
       have i₂ := eq4029 x
       grind)
    | exact superpose eq4029 eq32997
    | exact resolve eq32997 eq4029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4029 eq32997
  have eq33008 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq33002
       have i₂ := eq4425 x
       grind)
    | exact superpose eq4425 eq33002
    | exact resolve eq33002 eq4425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4425 eq33002
  have eq35942 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33008
       grind)
    | exact superpose eq33008 eq16
    | exact resolve eq16 eq33008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33008
  have eq36345 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35942
       have i₂ := eq30933
       grind)
    | exact superpose eq30933 eq35942
    | exact resolve eq35942 eq30933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30933 eq35942
  have eq36346 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq36345
  have eq36347 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq36346
  have eq36361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5107 x
       have i₂ := eq36347
       grind)
    | exact superpose eq36347 eq5107
    | exact resolve eq5107 eq36347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36347
  have eq36386 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq36361
       have r₂ := eq16
       grind)
    | exact resolve eq36361 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36361
  have eq36773 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq36386
       grind)
    | exact superpose eq36386 eq10
    | exact resolve eq10 eq36386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36386
  have eq36904 : y = (M.op x x) := by
    first
    | (have i₁ := eq36773
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq36773
    | exact resolve eq36773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36773
  have eq37002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5107 x
       have i₂ := eq36904
       grind)
    | exact superpose eq36904 eq5107
    | exact resolve eq5107 eq36904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107 eq36904
  have eq37028 : False := by grind
  exact eq37028

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  have eq51 : y = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq110 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq10597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10597
    | exact resolve eq10597 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10597
  have eq10609 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10598
       have r₂ := eq28
       grind)
    | exact resolve eq10598 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10598
  have eq10611 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10609
    | exact resolve eq10609 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10609
  have eq10613 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10611
  have eq10629 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10613
    | exact resolve eq10613 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10613
  have eq10641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10629 eq90
    | exact resolve eq90 eq10629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10629
  have eq10654 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10641
  have eq10656 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10654
       have r₂ := eq28
       grind)
    | exact resolve eq10654 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10654
  have eq10772 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10656
  have eq10788 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10772
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10772
    | exact resolve eq10772 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10772
  have eq10797 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq10788
       grind)
    | exact superpose eq10788 eq45
    | exact resolve eq45 eq10788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10788
  have eq10821 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10797
    | exact resolve eq10797 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10797
  have eq10989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10821 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq10821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10989
    | exact resolve eq10989 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10989
  have eq11003 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10992
       have r₂ := eq28
       grind)
    | exact resolve eq10992 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10992
  have eq11005 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11003
    | exact resolve eq11003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11003
  have eq11006 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11005
  have eq11009 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11006
  have eq11025 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11009
    | exact resolve eq11009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11009
  have eq11160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11025 eq10821
    | exact resolve eq10821 eq11025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10821 eq11025
  have eq11167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11160
  have eq11171 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11167
       have r₂ := eq28
       grind)
    | exact resolve eq11167 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11167
  have eq11174 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11171 eq52
    | exact resolve eq52 eq11171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq11175 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11171 eq111
    | (have r₁ := eq111
       have r₂ := eq11171
       grind)
    | exact resolve eq111 eq11171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq11171
  have eq11180 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11175
  have eq11296 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11174 eq14
    | exact resolve eq14 eq11174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11174
  have eq38802 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11180 eq57
    | exact resolve eq57 eq11180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq11180
  have eq75603 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11296 eq38802
    | exact resolve eq38802 eq11296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11296 eq38802
  have eq75792 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq75603
  have eq75801 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq75792
    | exact resolve eq75792 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq75792
  have eq75803 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq75801
  have eq75819 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq75803
    | exact resolve eq75803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75803
  have eq75833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75819 eq90
    | exact resolve eq90 eq75819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq75854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k x y) := by grind
  clear eq75833
  have eq75858 : y = (k x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq75854
       have r₂ := eq28
       grind)
    | exact resolve eq75854 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75854
  have eq76267 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq75858
       grind)
    | exact superpose eq75858 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq75858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75858
  have eq76268 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq76267
  have eq76274 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76268
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76268
    | exact resolve eq76268 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76268
  have eq76275 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq76274
  have eq76301 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq76275
  have eq76317 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76301
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76301
    | exact resolve eq76301 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76301
  have eq76717 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq76317
       grind)
    | exact superpose eq76317 eq45
    | exact resolve eq45 eq76317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76750 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq76717
    | exact resolve eq76717 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76717
  have eq76788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76750 eq75819
    | exact resolve eq75819 eq76750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75819 eq76750
  have eq76797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq76788
  have eq76806 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq76797
       have r₂ := eq28
       grind)
    | exact resolve eq76797 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76797
  have eq76836 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76317
       have i₂ := eq76806
       grind)
    | exact superpose eq76806 eq76317
    | exact resolve eq76317 eq76806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76317 eq76806
  have eq76846 : y = (M.op x y) := by grind
  clear eq76836
  have eq77264 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq76846 eq21
    | exact resolve eq21 eq76846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq77266 : y = (M.op y (M.op y (M.op y y))) := by
    first
    | exact superpose eq76846 eq51
    | exact resolve eq51 eq76846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq77274 : y ≠ y ∨ y = (M.op x x) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq76846 eq110
    | (have r₁ := eq110
       have r₂ := eq76846
       grind)
    | exact resolve eq110 eq76846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq77382 : y = (M.op x x) ∨ (k x y) = (M.op y y) := by grind
  clear eq77274
  have eq77490 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq77264
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq77264
    | exact resolve eq77264 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77264
  have eq77493 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq77490 eq27
    | exact resolve eq27 eq77490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq78323 : y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq77266
       grind)
    | exact superpose eq77266 eq14
    | exact resolve eq14 eq77266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77266
  have eq78406 : (k y y) = (M.op y y) := by grind
  have eq78419 : y = (k y y) := by
    first
    | (have i₁ := eq78406
       have i₂ := eq78323
       grind)
    | exact superpose eq78323 eq78406
    | exact resolve eq78406 eq78323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78406
  have eq78492 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq512 y y
       have i₂ := eq78419
       grind)
    | exact superpose eq78419 eq512
    | (have j0 := eq512 y y
       grind)
    | exact resolve eq512 eq78419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78419
  have eq78495 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq78492
  have eq78496 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq78495
  have eq78505 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78496
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq78496
    | exact resolve eq78496 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78496
  have eq78522 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq77490 eq78505
    | exact resolve eq78505 eq77490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78505
  have eq80005 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77382
       have i₂ := eq78323
       grind)
    | exact superpose eq78323 eq77382
    | exact resolve eq77382 eq78323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77382 eq78323
  have eq80662 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq80005
       grind)
    | exact superpose eq80005 eq45
    | exact resolve eq45 eq80005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq80680 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq512 x y
       have i₂ := eq80005
       grind)
    | exact superpose eq80005 eq512
    | (have j0 := eq512 x y
       grind)
    | exact resolve eq512 eq80005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq80005
  have eq80683 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq80680
  have eq80691 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80683
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80683
    | exact resolve eq80683 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80683
  have eq80707 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77490 eq80662
    | exact resolve eq80662 eq77490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80662
  have eq80709 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77490 eq80691
    | exact resolve eq80691 eq77490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80691
  have eq80725 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80707
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80707
    | exact resolve eq80707 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80707
  have eq80726 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80709
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80709
    | exact resolve eq80709 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80709
  have eq80739 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77490 eq80725
    | exact resolve eq80725 eq77490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80725
  have eq80740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77493 eq80726
    | exact resolve eq80726 eq77493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80726
  have eq80746 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq80740
       have r₂ := eq28
       grind)
    | exact resolve eq80740 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80740
  have eq80749 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80746
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80746
    | exact resolve eq80746 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80746
  have eq80752 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80749
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80749
    | exact resolve eq80749 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80749
  have eq80754 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77490 eq80752
    | exact resolve eq80752 eq77490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80752
  have eq80836 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq80754
  have eq80854 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77493 eq80836
    | exact resolve eq80836 eq77493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80836
  have eq80877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq80854 eq80739
    | exact resolve eq80739 eq80854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80739 eq80854
  have eq80886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq80877
  have eq80890 : y = (M.op x x) := by
    first
    | (have r₁ := eq80886
       have r₂ := eq28
       grind)
    | exact resolve eq80886 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80886
  have eq81553 : x = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq80890
       grind)
    | exact superpose eq80890 eq14
    | exact resolve eq14 eq80890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80890
  have eq81566 : x = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq81553
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81553
    | exact resolve eq81553 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81553
  have eq81575 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq76846 eq81566
    | exact resolve eq81566 eq76846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81566
  have eq81584 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq81575
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81575
    | exact resolve eq81575 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81575
  have eq81591 : x = (M.op x y) := by
    first
    | exact superpose eq76846 eq81584
    | exact resolve eq81584 eq76846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81584
  have eq81595 : x = (M.op x y) := by
    first
    | (have i₁ := eq81591
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81591
    | exact resolve eq81591 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq81591
  have eq81599 : x = y := by
    first
    | exact superpose eq76846 eq81595
    | exact resolve eq81595 eq76846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76846 eq81595
  have eq81611 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq81599
       grind)
    | exact superpose eq81599 eq25
    | exact resolve eq25 eq81599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq81599
  have eq82146 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq77490 eq81611
    | exact resolve eq81611 eq77490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77490 eq81611
  have eq82350 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq82146
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq82146
    | exact resolve eq82146 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq82146
  have eq82771 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq82350 eq77493
    | exact resolve eq77493 eq82350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77493 eq82350
  have eq82778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78522 eq82771
    | exact resolve eq82771 eq78522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78522 eq82771
  have eq82842 : False := by grind
  exact eq82842

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_y_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq427 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq436 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq436 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq436 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq436 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq447 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq427 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq427 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq427 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq513 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq447 X0 X1
       grind)
    | exact superpose eq447 eq9
    | (have j1 := eq447 X0 X1
       grind)
    | exact resolve eq9 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq518 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq513 X0 X1
       have j1 := eq438 X1 X0
       grind)
    | (have r₁ := eq513 X1 X1
       have r₂ := eq438 X0 X1
       grind)
    | exact resolve eq513 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq513
  have eq535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq518 (σ X1) (σ X0)
       grind)
    | exact superpose eq518 eq15
    | exact resolve eq15 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 X1
       have i₂ := eq518 X1 X0
       grind)
    | exact superpose eq518 eq535
    | exact resolve eq535 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq535
  have eq800 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq562 x y
       grind)
    | exact superpose eq562 eq16
    | (have r₁ := eq16
       have r₂ := eq562 x y
       grind)
    | exact resolve eq16 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq816 : False := by grind
  exact eq816

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 ∨ (k X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq65 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq64 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq73 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq19
    | (have j1 := eq66 (τ X0)
       grind)
    | exact resolve eq19 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq77 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq73
    | (have j0 := eq73 X0
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq83 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq77
    | (have j0 := eq77 X0
       grind)
    | exact resolve eq77 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq94 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (σ X1) (M.op X0 (σ X1))
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq95 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) (M.op X0 (τ X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq391 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq11
    | (have j1 := eq83 X0
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq392 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq391 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq391
    | (have j0 := eq391 X0
       grind)
    | exact resolve eq391 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq490 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq392 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq392
    | (have j0 := eq392 (σ X0)
       grind)
    | exact resolve eq392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq519 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq490 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq490
    | (have j0 := eq490 X0
       grind)
    | exact resolve eq490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq521 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq519 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq519
    | (have j0 := eq519 X0
       grind)
    | exact resolve eq519 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq623 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq743 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq744 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq747 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq744 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq744 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq744 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq750 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq747 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq747
    | (have j0 := eq747 X0 X1
       grind)
    | exact resolve eq747 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq4625 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq63 X0 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq63
    | (have j1 := eq65 X0
       grind)
    | (have r₁ := eq63 X0 X0
       have r₂ := eq65 X0
       grind)
    | exact resolve eq63 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq65
  have eq4626 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4625 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4625
  have eq4627 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4626
  have eq4706 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4627 (σ X0)
       grind)
    | exact superpose eq4627 eq15
    | exact resolve eq15 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4712 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq4627 (τ X0)
       grind)
    | exact superpose eq4627 eq32
    | exact resolve eq32 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq4719 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4712 X0
       have i₂ := eq4627 X0
       grind)
    | exact superpose eq4627 eq4712
    | exact resolve eq4712 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4712
  have eq4725 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4706 X0
       have i₂ := eq4627 X0
       grind)
    | exact superpose eq4627 eq4706
    | exact resolve eq4706 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4706
  have eq4802 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq4725 X0
       grind)
    | exact superpose eq4725 eq9
    | exact resolve eq9 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7760 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq7838 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7760 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7760
    | (have j0 := eq7760 X0 X1
       grind)
    | exact resolve eq7760 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7760
  have eq11298 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq95 X1 X0
       grind)
    | exact superpose eq95 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq95 X1 X0
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq95 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq11302 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq11298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11298
  have eq11305 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11302 X0 X1
       have i₂ := eq4719 X0
       grind)
    | exact superpose eq4719 eq11302
    | (have j0 := eq11302 X0 X1
       grind)
    | exact resolve eq11302 eq4719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719 eq11302
  have eq26756 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq743
       have i₂ := eq7838 x y
       grind)
    | exact superpose eq7838 eq743
    | (have j1 := eq7838 (σ x) (σ y)
       grind)
    | (have r₁ := eq743
       have r₂ := eq7838 x y
       grind)
    | (have r₁ := eq743
       have r₂ := eq7838 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq743
       have r₂ := eq7838 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq743 eq7838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26757 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq26756
  have eq31143 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq94 X1 X0
       grind)
    | exact superpose eq94 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq94 X1 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq94 (M.op X0 (σ X1)) X1
       grind)
    | exact resolve eq12 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq31148 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq31143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31143
  have eq31153 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31148 X0 X1
       have i₂ := eq4725 X0
       grind)
    | exact superpose eq4725 eq31148
    | (have j0 := eq31148 X0 X1
       grind)
    | exact resolve eq31148 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31148
  have eq32622 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26757
       grind)
    | exact superpose eq26757 eq16
    | exact resolve eq16 eq26757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26757
  have eq32623 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32622
       have r₂ := eq4725 x
       grind)
    | exact resolve eq32622 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32622
  have eq32624 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq32623
       grind)
    | exact superpose eq32623 eq9
    | exact resolve eq9 eq32623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32625 : y ≠ y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq32623
       grind)
    | exact superpose eq32623 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq32623
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq32623
       grind)
    | exact resolve eq12 eq32623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32623
  have eq32628 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32625
  have eq32630 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq743
       have i₂ := eq32628
       grind)
    | exact superpose eq32628 eq743
    | exact resolve eq743 eq32628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq32634 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq746 x y
       have i₂ := eq32628
       grind)
    | exact superpose eq32628 eq746
    | (have j0 := eq746 x y
       grind)
    | exact resolve eq746 eq32628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq32628
  have eq32637 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32634
  have eq32638 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32630
  have eq33858 : ∀ X0 X1 : G, (σ X1) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq750 (τ X0) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq750
    | (have j0 := eq750 (τ X0) X1
       grind)
    | exact resolve eq750 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq33876 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) ≠ (k X0 (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33858 X0 X1
       have i₂ := eq4725 X1
       grind)
    | exact superpose eq4725 eq33858
    | (have j0 := eq33858 X0 X1
       grind)
    | exact resolve eq33858 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33858
  have eq33920 : ∀ X0 X1 : G, (σ X1) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33876 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33876
    | (have j0 := eq33876 X0 X1
       grind)
    | exact resolve eq33876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33876
  have eq63805 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq32624
       grind)
    | exact superpose eq32624 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq32624
       grind)
    | exact resolve eq12 eq32624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32624
  have eq63808 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op y (M.op y y))) := by grind
  clear eq63805
  have eq63812 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq63808
       have i₂ := eq4725 y
       grind)
    | exact superpose eq4725 eq63808
    | exact resolve eq63808 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63808
  have eq63816 : y = (M.op y (M.op y (M.op y y))) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq63812
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq63812
    | exact resolve eq63812 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63812
  have eq84273 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11305 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11305
    | (have j0 := eq11305 (M.op (σ X0) (σ X0)) (k X1 X0)
       grind)
    | exact resolve eq11305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11305
  have eq84465 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq84273 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq84273
    | (have j0 := eq84273 X0 X1
       grind)
    | exact resolve eq84273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84273
  have eq84514 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84465 X0 X1
       have i₂ := eq4725 X0
       grind)
    | exact superpose eq4725 eq84465
    | (have j0 := eq84465 X0 X1
       grind)
    | exact resolve eq84465 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84465
  have eq84541 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84514 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq84514
    | (have j0 := eq84514 X0 X1
       grind)
    | exact resolve eq84514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84514
  have eq84678 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq84541 X1 X0
       grind)
    | exact superpose eq84541 eq10
    | (have j1 := eq84541 X1 X0
       grind)
    | exact resolve eq10 eq84541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84541
  have eq84796 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84678 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq84678
    | (have j0 := eq84678 X0 X1
       grind)
    | exact resolve eq84678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84678
  have eq85267 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq84796 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84796
  have eq85672 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85267 X0 (σ X0)
       have i₂ := eq4725 X0
       grind)
    | exact superpose eq4725 eq85267
    | (have j0 := eq85267 (k X1 (σ X0)) (σ (M.op X0 X0))
       grind)
    | exact resolve eq85267 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85267
  have eq92090 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq31153 X1 X0
       grind)
    | exact superpose eq31153 eq11
    | (have j1 := eq31153 X1 X0
       grind)
    | exact resolve eq11 eq31153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31153
  have eq92305 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92090 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq92090
    | (have j0 := eq92090 X0 X1
       grind)
    | exact resolve eq92090 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq92090
  have eq92776 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33920 X0 X1
       have i₂ := eq92305 X0 X1
       grind)
    | exact superpose eq92305 eq33920
    | (have j0 := eq33920 X0 X1
       have j1 := eq92305 X0 X1
       grind)
    | (have r₁ := eq33920 X0 X1
       have r₂ := eq92305 (k X0 (σ X1)) X1
       grind)
    | exact resolve eq33920 eq92305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33920 eq92305
  have eq92838 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92776 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92776
  have eq92871 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92838 X0 X1
       have j1 := eq85672 X1 X0
       grind)
    | (have r₁ := eq92838 X0 X0
       have r₂ := eq85672 X0 (M.op X0 (σ X0))
       grind)
    | (have r₁ := eq92838 X1 X0
       have r₂ := eq85672 X0 X1
       grind)
    | (have r₁ := eq92838 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq85672 X0 X1
       grind)
    | exact resolve eq92838 eq85672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85672 eq92838
  have eq120816 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq63816
       grind)
    | exact superpose eq63816 eq9
    | exact resolve eq9 eq63816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63816
  have eq120853 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq32637
       have i₂ := eq120816
       grind)
    | exact superpose eq120816 eq32637
    | exact resolve eq32637 eq120816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120816
  have eq120880 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq120853
  have eq120881 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq120880
  have eq124244 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq92871 (σ x) y
       have i₂ := eq120881
       grind)
    | exact superpose eq120881 eq92871
    | (have j0 := eq92871 (σ y) x
       grind)
    | (have r₁ := eq92871 (σ x) y
       have r₂ := eq120881
       grind)
    | exact resolve eq92871 eq120881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92871 eq120881
  have eq124254 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq124244
  have eq124255 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq124254
  have eq124264 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq124255
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq124255
    | exact resolve eq124255 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124255
  have eq124265 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq124264
  have eq124275 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq124265
       grind)
    | exact superpose eq124265 eq10
    | exact resolve eq10 eq124265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124265
  have eq124422 : x = y ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq124275
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq124275
    | exact resolve eq124275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124275
  have eq124478 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124422
       grind)
    | exact superpose eq124422 eq16
    | exact resolve eq16 eq124422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124422
  have eq124499 : (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq124478
       have r₂ := eq4725 x
       grind)
    | exact resolve eq124478 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124478
  have eq124511 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7838 x y
       have i₂ := eq124499
       grind)
    | exact superpose eq124499 eq7838
    | (have j0 := eq7838 x y
       grind)
    | exact resolve eq7838 eq124499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7838
  have eq124515 : (k x y) = (τ (σ (M.op y y))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq124499
       grind)
    | exact superpose eq124499 eq10
    | exact resolve eq10 eq124499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124499
  have eq124662 : (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq124515
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq124515
    | exact resolve eq124515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124515
  have eq124708 : y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq124662
       grind)
    | exact superpose eq124662 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq124662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124662
  have eq127161 : x = y ∨ y = (M.op y (M.op y (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq124708
       grind)
    | exact superpose eq124708 eq9
    | exact resolve eq9 eq124708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124708
  have eq132005 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y (M.op y (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127161
       grind)
    | exact superpose eq127161 eq16
    | exact resolve eq16 eq127161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127161
  have eq132043 : y = (M.op y (M.op y (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq132005
       have r₂ := eq4725 x
       grind)
    | exact resolve eq132005 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132005
  have eq132082 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq132043
       grind)
    | exact superpose eq132043 eq9
    | exact resolve eq9 eq132043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132043
  have eq132130 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq623 y
       have i₂ := eq132082
       grind)
    | exact superpose eq132082 eq623
    | (have j0 := eq623 y
       grind)
    | exact resolve eq623 eq132082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq132082
  have eq132153 : (σ y) = (σ (k y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq132130
  have eq132167 : (M.op x y) = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq132153
       have i₂ := eq4627 y
       grind)
    | exact superpose eq4627 eq132153
    | exact resolve eq132153 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627 eq132153
  have eq132212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq32638
       have i₂ := eq132167
       grind)
    | exact superpose eq132167 eq32638
    | exact resolve eq32638 eq132167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32638 eq132167
  have eq132269 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq132212
  have eq132312 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq132269
       have r₂ := eq32637
       grind)
    | exact resolve eq132269 eq32637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32637 eq132269
  have eq132325 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq132312
       grind)
    | exact superpose eq132312 eq16
    | exact resolve eq16 eq132312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132330 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq132312
       grind)
    | exact superpose eq132312 eq9
    | exact resolve eq9 eq132312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132312
  have eq132346 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132330
       have i₂ := eq4725 y
       grind)
    | exact superpose eq4725 eq132330
    | exact resolve eq132330 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132330
  have eq132361 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq132325
       have i₂ := eq124511
       grind)
    | exact superpose eq124511 eq132325
    | exact resolve eq132325 eq124511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124511
  have eq132385 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq132361
  have eq154091 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq132385
       grind)
    | exact superpose eq132385 eq10
    | exact resolve eq10 eq132385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132385
  have eq154238 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq154091
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq154091
    | exact resolve eq154091 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154091
  have eq154239 : x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq154238
  have eq154269 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154239
       grind)
    | exact superpose eq154239 eq16
    | exact resolve eq16 eq154239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154239
  have eq154310 : (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq154269
       have r₂ := eq4725 x
       grind)
    | exact resolve eq154269 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154269
  have eq170140 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4802 y
       have i₂ := eq132346
       grind)
    | exact superpose eq132346 eq4802
    | exact resolve eq4802 eq132346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4802 eq132346
  have eq170190 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq170140
       have i₂ := eq4725 y
       grind)
    | exact superpose eq4725 eq170140
    | exact resolve eq170140 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170140
  have eq170244 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq170190
       have i₂ := eq154310
       grind)
    | exact superpose eq154310 eq170190
    | exact resolve eq170190 eq154310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154310 eq170190
  have eq170293 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq170244
       have r₂ := eq132325
       grind)
    | exact resolve eq170244 eq132325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132325 eq170244
  have eq170331 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq170293
       grind)
    | exact superpose eq170293 eq16
    | exact resolve eq16 eq170293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170333 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq170293
       grind)
    | exact superpose eq170293 eq10
    | exact resolve eq10 eq170293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170293
  have eq170488 : x = y := by
    first
    | (have i₁ := eq170333
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq170333
    | exact resolve eq170333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170333
  have eq170489 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq170331
       have i₂ := eq4725 x
       grind)
    | exact superpose eq4725 eq170331
    | exact resolve eq170331 eq4725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4725 eq170331
  have eq170526 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq170489
       have i₂ := eq170488
       grind)
    | exact superpose eq170488 eq170489
    | exact resolve eq170489 eq170488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170488 eq170489
  have eq170527 : False := by grind
  exact eq170527

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq143 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq85 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq145 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq184 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq145 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq145
    | (have j0 := eq145 (τ X0)
       grind)
    | exact resolve eq145 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq145
  have eq186 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq184 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq184
    | (have j0 := eq184 X0
       grind)
    | exact resolve eq184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq189 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq186
    | (have j0 := eq186 X0
       grind)
    | exact resolve eq186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq200 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq189 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq189
    | (have j0 := eq189 (τ X0)
       grind)
    | exact resolve eq189 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq672 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq143 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq143
    | (have j0 := eq143 (τ X0) (τ X1)
       grind)
    | exact resolve eq143 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq672
    | (have j0 := eq672 X0 X1
       grind)
    | exact resolve eq672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq687 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq690 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq687 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq687
    | (have j0 := eq687 X0 X1
       grind)
    | exact resolve eq687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq692 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq690
    | (have j0 := eq690 X0 X1
       grind)
    | exact resolve eq690 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq694 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq692
    | (have j0 := eq692 X0 X1
       grind)
    | exact resolve eq692 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq695 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq4089 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq86 X1 X0
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq86 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq86 X0 (σ X0)
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4111 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq4112 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq4114 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4089 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq4115 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114
  have eq4118 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4112 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4112
    | (have j0 := eq4112 X0
       grind)
    | exact resolve eq4112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4112
  have eq4156 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq4118 X0
       grind)
    | exact superpose eq4118 eq38
    | (have j1 := eq4118 X0
       grind)
    | exact resolve eq38 eq4118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq4118
  have eq4167 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4156 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4156
    | (have j0 := eq4156 X0
       grind)
    | exact resolve eq4156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4156
  have eq4168 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4167
  have eq4170 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4168 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4168
    | exact resolve eq4168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4193 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4168 X0
       grind)
    | exact superpose eq4168 eq11
    | exact resolve eq11 eq4168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq4254 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4170 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq4170
    | exact resolve eq4170 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170
  have eq4474 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq200 X0
       have i₂ := eq4254 X0
       grind)
    | exact superpose eq4254 eq200
    | (have j0 := eq200 X0
       grind)
    | exact resolve eq200 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq4478 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4254 X0
       grind)
    | exact superpose eq4254 eq11
    | exact resolve eq11 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4589 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4478 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4478
    | exact resolve eq4478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq4651 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq4589 (τ X0)
       grind)
    | exact superpose eq4589 eq34
    | exact resolve eq34 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4707 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4651 X0
       have i₂ := eq4254 X0
       grind)
    | exact superpose eq4254 eq4651
    | exact resolve eq4651 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254 eq4651
  have eq5246 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5263 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5246 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5246
    | exact resolve eq5246 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246
  have eq5292 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5263 X0
       have i₂ := eq4589 X0
       grind)
    | exact superpose eq4589 eq5263
    | exact resolve eq5263 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5263
  have eq5306 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5292
  have eq22404 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) X0
       have i₂ := eq4115 (σ X0) X1
       grind)
    | exact superpose eq4115 eq24
    | (have j1 := eq4115 (σ X0) X1
       grind)
    | exact resolve eq24 eq4115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4115
  have eq22488 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22404 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq22404
    | (have j0 := eq22404 X0 X1
       grind)
    | exact resolve eq22404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22404
  have eq22564 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22488 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22488
    | (have j0 := eq22488 X0 X1
       grind)
    | exact resolve eq22488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22488
  have eq22631 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22564 X0 X1
       have i₂ := eq4193 X0
       grind)
    | exact superpose eq4193 eq22564
    | (have j0 := eq22564 X0 X1
       grind)
    | exact resolve eq22564 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22564
  have eq22677 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22631 X0 X1
       have i₂ := eq4589 X0
       grind)
    | exact superpose eq4589 eq22631
    | (have j0 := eq22631 X0 X1
       grind)
    | exact resolve eq22631 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22631
  have eq22714 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22677 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22677
    | (have j0 := eq22677 X0 X1
       grind)
    | exact resolve eq22677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22677
  have eq25572 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22714 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22714
    | (have j0 := eq22714 X1 (τ X0)
       grind)
    | exact resolve eq22714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25653 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq22714 X1 X0
       grind)
    | exact superpose eq22714 eq11
    | (have j1 := eq22714 X1 X0
       grind)
    | exact resolve eq11 eq22714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22714
  have eq26080 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25572 X1 (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq25572
    | (have j0 := eq25572 X0 (τ X1)
       grind)
    | exact resolve eq25572 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq25572
  have eq26263 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26080 X0 X1
       have i₂ := eq4707 X1
       grind)
    | exact superpose eq4707 eq26080
    | (have j0 := eq26080 X0 X1
       grind)
    | exact resolve eq26080 eq4707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26080
  have eq26344 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26263 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq26263
    | (have j0 := eq26263 X0 X1
       grind)
    | exact resolve eq26263 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26263
  have eq26415 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26344 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq26344
    | (have j0 := eq26344 X0 X1
       grind)
    | exact resolve eq26344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26344
  have eq26902 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26415 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26415
  have eq28781 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25653 x y
       grind)
    | exact superpose eq25653 eq16
    | (have j1 := eq25653 x y
       grind)
    | exact resolve eq16 eq25653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25653
  have eq29180 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28781
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq28781
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq28781 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28781
  have eq29183 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq29180
  have eq29184 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq29183
  have eq29737 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26902 x y
       have i₂ := eq29184
       grind)
    | exact superpose eq29184 eq26902
    | (have j0 := eq26902 x y
       grind)
    | exact resolve eq26902 eq29184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26902 eq29184
  have eq29738 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq29737
  have eq29739 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq29738
  have eq30169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5306 y
       have i₂ := eq29739
       grind)
    | exact superpose eq29739 eq5306
    | exact resolve eq5306 eq29739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29739
  have eq30190 : (σ x) = (σ (M.op y y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq30169
       have r₂ := eq16
       grind)
    | exact resolve eq30169 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30169
  have eq30209 : (M.op y y) = (τ (σ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq30190
       grind)
    | exact superpose eq30190 eq10
    | exact resolve eq10 eq30190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30190
  have eq30333 : x = (M.op y y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq30209
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30209
    | exact resolve eq30209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30209
  have eq30778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq5306 y
       have i₂ := eq30333
       grind)
    | exact superpose eq30333 eq5306
    | exact resolve eq5306 eq30333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30333
  have eq30799 : (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq30778
       have r₂ := eq16
       grind)
    | exact resolve eq30778 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30778
  have eq30815 : (k x y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq30799
       grind)
    | exact superpose eq30799 eq11
    | exact resolve eq11 eq30799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30799
  have eq30987 : y = (k x y) := by
    first
    | (have i₁ := eq30815
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq30815
    | exact resolve eq30815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30815
  have eq31435 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq143 x y
       have i₂ := eq30987
       grind)
    | exact superpose eq30987 eq143
    | (have j0 := eq143 x y
       grind)
    | exact resolve eq143 eq30987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq31440 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq695 x y
       have i₂ := eq30987
       grind)
    | exact superpose eq30987 eq695
    | (have j0 := eq695 x y
       grind)
    | (have r₁ := eq695 x y
       have r₂ := eq30987
       grind)
    | exact resolve eq695 eq30987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq30987
  have eq31443 : y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq31440
  have eq31445 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq31435
  have eq31451 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31445
       have i₂ := eq4193 y
       grind)
    | exact superpose eq4193 eq31445
    | exact resolve eq31445 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31445
  have eq31457 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq31451
       have i₂ := eq4589 y
       grind)
    | exact superpose eq4589 eq31451
    | exact resolve eq31451 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31451
  have eq31471 : y = (M.op y (M.op y (M.op y y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq31443
       grind)
    | exact superpose eq31443 eq9
    | exact resolve eq9 eq31443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34300 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq31471
       grind)
    | exact superpose eq31471 eq9
    | exact resolve eq9 eq31471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31471
  have eq34325 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4474 y
       have i₂ := eq34300
       grind)
    | exact superpose eq34300 eq4474
    | (have j0 := eq4474 y
       grind)
    | exact resolve eq4474 eq34300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4474 eq34300
  have eq34347 : (τ y) = (M.op (τ y) (τ y)) ∨ x = (M.op y y) := by grind
  clear eq34325
  have eq34360 : x = (M.op y y) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq34347
       have i₂ := eq4707 y
       grind)
    | exact superpose eq4707 eq34347
    | exact resolve eq34347 eq4707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4707 eq34347
  have eq34767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq5306 y
       have i₂ := eq34360
       grind)
    | exact superpose eq34360 eq5306
    | exact resolve eq5306 eq34360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5306 eq34360
  have eq34789 : (τ y) = (τ (M.op y y)) := by
    first
    | (have r₁ := eq34767
       have r₂ := eq16
       grind)
    | exact resolve eq34767 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34767
  have eq35169 : (M.op y y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (M.op y y)
       have i₂ := eq34789
       grind)
    | exact superpose eq34789 eq11
    | exact resolve eq11 eq34789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34789
  have eq35353 : y = (M.op y y) := by
    first
    | (have i₁ := eq35169
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq35169
    | exact resolve eq35169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35169
  have eq38226 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31457
       grind)
    | exact superpose eq31457 eq16
    | exact resolve eq16 eq31457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31457
  have eq38252 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38226
       have i₂ := eq35353
       grind)
    | exact superpose eq35353 eq38226
    | exact resolve eq38226 eq35353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38226
  have eq38388 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38252
       have i₂ := eq31443
       grind)
    | exact superpose eq31443 eq38252
    | exact resolve eq38252 eq31443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31443 eq38252
  have eq38391 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq38388
  have eq38394 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38391
       have i₂ := eq35353
       grind)
    | exact superpose eq35353 eq38391
    | exact resolve eq38391 eq35353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35353 eq38391
  have eq38761 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38394
       grind)
    | exact superpose eq38394 eq16
    | exact resolve eq16 eq38394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38394
  have eq38810 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38761
       have i₂ := eq4193 x
       grind)
    | exact superpose eq4193 eq38761
    | exact resolve eq38761 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38761
  have eq38815 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38810
       have i₂ := eq4589 x
       grind)
    | exact superpose eq4589 eq38810
    | exact resolve eq38810 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38810
  have eq38816 : (σ x) = (σ y) := by grind
  clear eq38815
  have eq38819 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38816
       grind)
    | exact superpose eq38816 eq16
    | exact resolve eq16 eq38816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38820 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq38816
       grind)
    | exact superpose eq38816 eq10
    | exact resolve eq10 eq38816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38816
  have eq38958 : x = y := by
    first
    | (have i₁ := eq38820
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38820
    | exact resolve eq38820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38820
  have eq38959 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq38819
       have i₂ := eq4193 x
       grind)
    | exact superpose eq4193 eq38819
    | exact resolve eq38819 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193 eq38819
  have eq39004 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq38959
       have i₂ := eq4589 x
       grind)
    | exact superpose eq4589 eq38959
    | exact resolve eq38959 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589 eq38959
  have eq39047 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq39004
       have i₂ := eq38958
       grind)
    | exact superpose eq38958 eq39004
    | exact resolve eq39004 eq38958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38958 eq39004
  have eq39048 : False := by grind
  exact eq39048

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq52 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq53 (σ X0)
       grind)
    | exact superpose eq53 eq15
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq53 (τ X0)
       grind)
    | exact superpose eq53 eq18
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq61
    | exact resolve eq61 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq61
  have eq78 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq89
  have eq131 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | (have j0 := eq91 X1 X1
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq147 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq131
  have eq153 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq147 X0 X0
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq147 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq147
  have eq157 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq153
    | (have j0 := eq153 X0 X1
       grind)
    | exact resolve eq153 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq153
  have eq405 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq157
    | exact resolve eq157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq450 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq405 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq405 X0 X1
       grind)
    | exact superpose eq405 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq405 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq405 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq405 X0 X1
       grind)
    | exact resolve eq13 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq450 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq456 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq454 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq454 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq454 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq499 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq456 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq503 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq499 X0 X1
       have j1 := eq405 X1 X0
       grind)
    | (have r₁ := eq499 X0 X0
       have r₂ := eq405 X0 X0
       grind)
    | (have r₁ := eq499 X1 X0
       have r₂ := eq405 X0 X1
       grind)
    | exact resolve eq499 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq499
  have eq624 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq503 (σ X1) (σ X0)
       grind)
    | exact superpose eq503 eq15
    | exact resolve eq15 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 X1
       have i₂ := eq503 X1 X0
       grind)
    | exact superpose eq503 eq624
    | exact resolve eq624 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq624
  have eq1200 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq645 x y
       grind)
    | exact superpose eq645 eq16
    | (have r₁ := eq16
       have r₂ := eq645 x y
       grind)
    | exact resolve eq16 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq1211 : False := by grind
  exact eq1211

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq385 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq418 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq385 X0 X1
       grind)
    | exact superpose eq385 eq9
    | (have j1 := eq385 X0 X1
       grind)
    | exact resolve eq9 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq552 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq418 X0 X1
       grind)
    | exact superpose eq418 eq9
    | (have j1 := eq418 X0 X1
       grind)
    | exact resolve eq9 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq556 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq552 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq552 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq552 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq601 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq556 (σ X1) (σ X0)
       grind)
    | exact superpose eq556 eq15
    | exact resolve eq15 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq601 X0 X1
       have i₂ := eq556 X1 X0
       grind)
    | exact superpose eq556 eq601
    | exact resolve eq601 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq601
  have eq968 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq628 x y
       grind)
    | exact superpose eq628 eq16
    | (have r₁ := eq16
       have r₂ := eq628 x y
       grind)
    | exact resolve eq16 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq984 : False := by grind
  exact eq984
