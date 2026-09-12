import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (M.op x y) ≠ (M.op x x) ∨ (M.op y x) = (k y x) := by
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
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
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
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
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
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq78
    | (have j0 := eq78 (σ X0) (σ X1)
       grind)
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq78
    | (have j0 := eq78 (σ x) (σ X0)
       grind)
    | exact resolve eq78 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq44
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq44 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq100 eq78
    | (have j0 := eq78 (σ x) (σ y)
       grind)
    | exact resolve eq78 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq103
    | exact resolve eq103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq104
       have r₂ := eq27
       grind)
    | exact resolve eq104 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq109 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq107
    | exact resolve eq107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq112 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op y x) := by
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
  have eq113 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq125 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq129 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq125
    | exact resolve eq125 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq131 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq129
    | exact resolve eq129 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq138 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq139 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq140
    | exact resolve eq140 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq143
       have i₂ := eq67 sF0
       grind)
    | exact superpose eq67 eq143
    | exact resolve eq143 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq143
  have eq153 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : (σ (k y (M.op y y))) = (k (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq131
       grind)
    | exact superpose eq131 eq36
    | exact resolve eq36 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq163 : (σ (k x (M.op y y))) = (k (σ x) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq35 (M.op y y)
       have i₂ := eq131
       grind)
    | exact superpose eq131 eq35
    | exact resolve eq35 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq131
       grind)
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq138
       have i₂ := eq78 sF0 x
       grind)
    | exact superpose eq78 eq138
    | (have j1 := eq78 (M.op x y) x
       grind)
    | exact resolve eq138 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq139 eq16
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq199 : ∀ X0 : G, (σ (k X0 (M.op (M.op x y) (M.op x y)))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq145 eq10
    | exact resolve eq10 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq145 eq16
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : (σ (k (k x (M.op x y)) y)) = (k (k (σ x) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq45 eq40
    | exact resolve eq40 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq78 (σ X0) sF3
       grind)
    | exact superpose eq78 eq40
    | (have j1 := eq78 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq78 (σ X0) sF1
       grind)
    | exact superpose eq78 eq41
    | (have j1 := eq78 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq258 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq258
    | exact resolve eq258 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq262 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq109 eq51
    | exact resolve eq51 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq271 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq268
    | exact resolve eq268 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq278 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (σ y)) X1)) = (M.op X1 (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq262 eq14
    | exact resolve eq14 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq283 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq278 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq278
    | exact resolve eq278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq299 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq78 (τ X0) X1
       grind)
    | exact superpose eq78 eq34
    | (have j1 := eq78 (τ X0) X1
       grind)
    | exact resolve eq34 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq307 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) y)) = (k (k X0 (σ X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq40
    | exact resolve eq40 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq40
  have eq319 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ (M.op X0 X0) ∨ (M.op (M.op (σ y) X1) X0) = (k (M.op (σ y) X1) X0) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq283 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ y) X0)
       have r₂ := eq283 X0 (M.op (σ y) X0)
       grind)
    | (have r₁ := eq13 (M.op (σ y) X0) (σ y)
       have r₂ := eq283 X0 (σ y)
       grind)
    | exact resolve eq13 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq410 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 (M.op (M.op X0 X1) X2)) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op (M.op X0 X1) X2)
       have i₂ := eq54 X2 X1 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X3 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq54 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq13 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq54 X0 X1 X1 X3
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 X1) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq410 X0 X1 X2 X3
       have i₂ := eq54 X2 X1 X3 X0
       grind)
    | exact superpose eq54 eq410
    | (have j0 := eq410 X0 X1 X2 X3
       grind)
    | (have r₁ := eq410 X0 X1 X2 (M.op (M.op X3 X1) X0)
       have r₂ := eq54 X0 X1 (M.op (M.op X0 X1) X2) X3
       grind)
    | (have r₁ := eq410 X0 (M.op (M.op X3 X1) X0) X2 X1
       have r₂ := eq54 X0 X1 (M.op (M.op X0 (M.op (M.op X3 X1) X0)) X2) X3
       grind)
    | exact resolve eq410 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq494 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq109 eq113
    | (have r₁ := eq113
       have r₂ := eq109
       grind)
    | exact resolve eq113 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq113
  have eq495 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq494
  have eq498 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq495 eq100
    | exact resolve eq100 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq501 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq498
  have eq507 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq501 eq166
    | exact resolve eq166 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq512 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X0)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq501 eq14
    | exact resolve eq14 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq517 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq512 X0
       have i₂ := eq14 X0 sF2 sF3
       grind)
    | exact superpose eq14 eq512
    | exact resolve eq512 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq552 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op (σ (k X0 X1)) X3)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X3 (σ X1) X2 (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq54
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq54 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq559 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq570 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq517
    | (have j0 := eq517 (σ x)
       grind)
    | exact resolve eq517 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq600 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq570 eq65
    | (have r₁ := eq65
       have r₂ := eq570
       grind)
    | exact resolve eq65 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq570
  have eq607 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq600
  have eq619 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq607 eq153
    | exact resolve eq153 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq607
  have eq665 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq619 eq507
    | exact resolve eq507 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq619
  have eq669 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq665
  have eq1136 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) y) ≠ (M.op (M.op (M.op x y) X0) X1) ∨ (M.op X1 (M.op (M.op x y) X0)) = (k X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq260 eq13
    | (have j0 := eq13 X1 (M.op (M.op x y) X0)
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) X0) y
       have r₂ := eq260 X0 y
       grind)
    | (have r₁ := eq13 y (M.op (M.op x y) X0)
       have r₂ := eq260 X0 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq13 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1160 : ∀ X0 X1 : G, (M.op X1 y) = (k X1 (M.op (M.op x y) X0)) ∨ (M.op (M.op (M.op x y) X0) y) ≠ (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq260 eq1136
    | (have j0 := eq1136 X0 X1
       grind)
    | (have r₁ := eq1136 X0 (M.op (M.op x y) X0)
       have r₂ := eq260 X0 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq1136 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1382 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (σ X0) X1 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq54
    | exact resolve eq54 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1478 : ∀ X0 : G, (k (τ X0) (M.op y y)) = (τ (k X0 (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq302 X0 (M.op y y)
       have i₂ := eq131
       grind)
    | exact superpose eq131 eq302
    | exact resolve eq302 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1492 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq302
    | (have j0 := eq302 X0 (M.op x y)
       grind)
    | exact resolve eq302 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq1704 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq350 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq350
    | (have j0 := eq350 x X0
       grind)
    | exact resolve eq350 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq1866 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (k (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq319 (σ y) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq2873 : ∀ X0 X1 : G, (k (k X0 (σ X1)) (σ y)) = (σ (M.op (k (τ X0) X1) y)) ∨ y = (M.op (k (τ X0) X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq78 (k (τ X0) X1) y
       grind)
    | exact superpose eq78 eq307
    | (have j1 := eq78 (k (τ X0) X1) y
       grind)
    | exact resolve eq307 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq6338 : ∀ X0 X1 : G, (σ (M.op (τ X0) y)) = (k X0 (σ (M.op (M.op x y) X1))) ∨ (M.op (M.op x y) X1) = (M.op (τ X0) y) := by
    intro X0 X1
    first
    | exact superpose eq260 eq299
    | exact resolve eq299 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq7603 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k (k X0 X1) (M.op x y)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op x y)) = (M.op (σ (k X0 X1)) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq243 eq552
    | (have j0 := eq552 X0 X1 X2 x
       have j1 := eq243 (k X0 X1)
       grind)
    | exact resolve eq552 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq552
  have eq8960 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq416 X1 X0 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq9952 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq10060 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9952 y x
       have i₂ := eq669
       grind)
    | exact superpose eq669 eq9952
    | (have j0 := eq9952 y x
       grind)
    | exact resolve eq9952 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq10074 : (k (σ x) (σ (M.op x y))) ≠ (σ (M.op x x)) ∨ (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq45 eq9952
    | (have j0 := eq9952 x (M.op x y)
       grind)
    | exact resolve eq9952 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10078 : (k (σ y) (σ x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9952 y x
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq9952
    | (have j0 := eq9952 y x
       grind)
    | exact resolve eq9952 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9952
  have eq10111 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq10060
  have eq10123 : (k (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10078
       have i₂ := eq131
       grind)
    | exact superpose eq131 eq10078
    | exact resolve eq10078 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10078
  have eq10127 : (k (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) ∨ (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10074
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq10074
    | exact resolve eq10074 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10074
  have eq10136 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10111
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10111
    | exact resolve eq10111 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10111
  have eq10185 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10123
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10123
    | exact resolve eq10123 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10123
  have eq10189 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10127
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10127
    | exact resolve eq10127 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10127
  have eq10198 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10136
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10136
    | exact resolve eq10136 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10136
  have eq10215 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10185
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10185
    | exact resolve eq10185 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10185
  have eq10219 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10189
    | exact resolve eq10189 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10189
  have eq10228 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10198
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10198
    | exact resolve eq10198 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10198
  have eq10240 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10215
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10215
    | exact resolve eq10215 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10215
  have eq10243 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq138 eq10219
    | exact resolve eq10219 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq10219
  have eq10250 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq10228
    | exact resolve eq10228 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10228
  have eq10260 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq10240
    | exact resolve eq10240 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10240
  have eq10263 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq10243
    | exact resolve eq10243 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10243
  have eq10268 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10250
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10250
    | exact resolve eq10250 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10250
  have eq10276 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10260
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10260
    | exact resolve eq10260 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10260
  have eq10279 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10263
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10263
    | exact resolve eq10263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10263
  have eq10284 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10268
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10268
    | exact resolve eq10268 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10268
  have eq10285 : (k (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10276
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10276
    | exact resolve eq10276 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10276
  have eq10293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq10284 eq100
    | exact resolve eq100 eq10284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10284
  have eq10299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq10293
  have eq10303 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq10299
       have r₂ := eq27
       grind)
    | exact resolve eq10299 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10299
  have eq10345 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq10303 eq1866
    | exact resolve eq1866 eq10303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10303
  have eq10374 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq10345
  have eq10420 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq10374
    | exact resolve eq10374 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10374
  have eq10458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq10420 eq100
    | exact resolve eq100 eq10420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10420
  have eq10464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq10458
  have eq10468 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10464
       have r₂ := eq27
       grind)
    | exact resolve eq10464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10464
  have eq10473 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10468 eq283
    | exact resolve eq283 eq10468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq10475 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10468 eq1866
    | exact resolve eq1866 eq10468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10487 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq10468 eq54
    | exact resolve eq54 eq10468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10500 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10475
  have eq10502 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10473 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10473
  have eq10786 : (k (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10500 eq193
    | exact resolve eq193 eq10500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq10500
  have eq10808 : ∀ X0 : G, (M.op (σ y) (σ (M.op x y))) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10502 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq10502 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ y)
       have r₂ := eq10502 (σ y)
       grind)
    | exact resolve eq13 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11054 : (k (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10502 eq10786
    | exact resolve eq10786 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502
  have eq11077 : (k (M.op x y) y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by grind
  clear eq11054
  have eq11080 : (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq200 eq11077
    | exact resolve eq11077 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11077
  have eq14686 : (k x (k (M.op x y) y)) = (τ (k (σ x) (M.op (σ (M.op x y)) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10786 eq1704
    | exact resolve eq1704 eq10786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10786
  have eq17576 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ (M.op x y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10468 eq8960
    | exact resolve eq8960 eq10468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10468
  have eq17738 : (τ (M.op (σ x) (σ x))) = (k x (k (M.op x y) y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17576 eq14686
    | exact resolve eq14686 eq17576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14686 eq17576
  have eq17750 : (τ (M.op (σ x) (σ x))) = (k x (k (M.op x y) y)) ∨ y = (M.op x y) := by grind
  clear eq17738
  have eq17777 : (M.op x x) = (k x (k (M.op x y) y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq72 eq17750
    | exact resolve eq17750 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17750
  have eq17959 : (M.op x x) = (k x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11080 eq17777
    | exact resolve eq17777 eq11080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11080 eq17777
  have eq17973 : (M.op x x) = (k x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq17959
  have eq18200 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17973 eq78
    | (have j0 := eq78 x (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq78 eq17973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17973
  have eq18217 : (M.op x y) = (M.op x x) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq260 eq18200
    | exact resolve eq18200 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18200
  have eq18225 : (M.op x y) = (M.op x x) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18217
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18217
    | exact resolve eq18217 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18217
  have eq18233 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq260 eq18225
    | exact resolve eq18225 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18225
  have eq18240 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18233
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18233
    | exact resolve eq18233 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18233
  have eq18572 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18240 eq145
    | exact resolve eq145 eq18240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq18240
  have eq18627 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq18572
    | exact resolve eq18572 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18572
  have eq18718 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18627 eq10487
    | exact resolve eq10487 eq18627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10487 eq18627
  have eq18744 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq18718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18718
  have eq200940 : (M.op (σ y) (σ (M.op x y))) ≠ (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18744 eq10808
    | (have j0 := eq10808 (σ (M.op x y))
       grind)
    | (have r₁ := eq10808 (σ x)
       have r₂ := eq18744 (σ y)
       grind)
    | exact resolve eq10808 eq18744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10808 eq18744
  have eq200952 : (M.op (σ y) (σ (M.op x y))) ≠ (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq200940
  have eq200953 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq200952
  have eq201001 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq200953
    | exact resolve eq200953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200953
  have eq202059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq201001 eq100
    | exact resolve eq100 eq201001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201001
  have eq202073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq202059
  have eq202076 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq202073
       have r₂ := eq27
       grind)
    | exact resolve eq202073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202073
  have eq202080 : (M.op x y) ≠ (M.op x y) ∨ (M.op y x) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq202076
       grind)
    | exact superpose eq202076 eq64
    | (have r₁ := eq64
       have r₂ := eq202076
       grind)
    | exact resolve eq64 eq202076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq202107 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq202076
       grind)
    | exact superpose eq202076 eq54
    | exact resolve eq54 eq202076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202076
  have eq202129 : (M.op y x) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq202080
  have eq202132 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq260 eq202107
    | exact resolve eq202107 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202107
  have eq202382 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq202129
       grind)
    | exact superpose eq202129 eq124
    | exact resolve eq124 eq202129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq202129
  have eq202564 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq131
       have i₂ := eq202132 y
       grind)
    | exact superpose eq202132 eq131
    | exact resolve eq131 eq202132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202132
  have eq208697 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq202382
       have i₂ := eq202564
       grind)
    | exact superpose eq202564 eq202382
    | exact resolve eq202382 eq202564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202382 eq202564
  have eq208830 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq208697
  have eq208856 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq208830 eq10285
    | (have r₁ := eq10285
       have r₂ := eq208830
       grind)
    | exact resolve eq10285 eq208830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10285 eq208830
  have eq208878 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq208856
  have eq220325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq208878 eq100
    | exact resolve eq100 eq208878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208878
  have eq220339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq220325
  have eq220342 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq220339
       have r₂ := eq27
       grind)
    | exact resolve eq220339 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220339
  have eq220392 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq220342 eq1866
    | exact resolve eq1866 eq220342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866 eq220342
  have eq220451 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq220392
  have eq220508 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq220451
    | exact resolve eq220451 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220451
  have eq223076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq220508 eq100
    | exact resolve eq100 eq220508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq220508
  have eq223090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq223076
  have eq223094 : y = (M.op x y) := by
    first
    | (have r₁ := eq223090
       have r₂ := eq27
       grind)
    | exact resolve eq223090 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223090
  have eq223096 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq223094 eq20
    | exact resolve eq20 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223098 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq223094 eq50
    | exact resolve eq50 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq223101 : y ≠ y ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq223094 eq112
    | (have r₁ := eq112
       have r₂ := eq223094
       grind)
    | exact resolve eq112 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq223118 : (k (σ (M.op x y)) (σ x)) = (σ (M.op y x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq223094 eq182
    | exact resolve eq182 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq223146 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq223094 eq260
    | exact resolve eq260 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223242 : (k x y) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq223101
  have eq223375 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq223096
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq223096
    | exact resolve eq223096 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223096
  have eq223407 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq223375 eq26
    | exact resolve eq26 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223429 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq223375 eq219
    | exact resolve eq219 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq229973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq223407 eq10279
    | exact resolve eq10279 eq223407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10279
  have eq229974 : (k (σ x) (σ (M.op x y))) ≠ (M.op (σ x) (σ x)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq229973
       have r₂ := eq27
       grind)
    | exact resolve eq229973 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229973
  have eq230699 : ∀ X0 X1 : G, (M.op X1 y) = (k X1 (M.op y X0)) ∨ (M.op (M.op (M.op x y) X0) y) ≠ (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq223094 eq1160
    | (have j0 := eq1160 X0 X1
       grind)
    | exact resolve eq1160 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq230700 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) ≠ (M.op (M.op y X0) y) ∨ (M.op X1 y) = (k X1 (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq223094 eq230699
    | (have j0 := eq230699 X0 X1
       grind)
    | exact resolve eq230699 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230699
  have eq230970 : ∀ X0 X1 : G, (M.op (M.op y X0) y) ≠ (M.op (M.op y X0) y) ∨ (M.op (M.op (M.op x y) X1) y) = (k (M.op (M.op x y) X1) (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq260 eq230700
    | (have j0 := eq230700 X0 y
       grind)
    | (have r₁ := eq230700 X0 (M.op (M.op x y) X0)
       have r₂ := eq260 X0 (M.op y X0)
       grind)
    | exact resolve eq230700 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq231089 : ∀ X0 : G, (M.op y y) = (k y (M.op y X0)) := by
    intro X0
    first
    | (have j0 := eq230700 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230700
  have eq231104 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) y) = (k (M.op (M.op x y) X1) (M.op y X0)) := by
    intro X0 X1
    first
    | (have j0 := eq230970 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230970
  have eq231111 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (k (M.op y X1) (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq223094 eq231104
    | exact resolve eq231104 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231104
  have eq231208 : (σ (M.op y y)) = (k (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq162
       have i₂ := eq231089 y
       grind)
    | exact superpose eq231089 eq162
    | exact resolve eq162 eq231089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq231089
  have eq231237 : (σ (M.op y y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq223375 eq231208
    | exact resolve eq231208 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231208
  have eq231246 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq231237
       have i₂ := eq131
       grind)
    | exact superpose eq131 eq231237
    | exact resolve eq231237 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231237
  have eq231254 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq223375 eq231246
    | exact resolve eq231246 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231246
  have eq231278 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq231254 eq78
    | (have j0 := eq78 (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq78 eq231254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231254
  have eq231290 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by grind
  clear eq231278
  have eq231315 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X0 (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq231290 eq54
    | exact resolve eq54 eq231290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231290
  have eq231335 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq231315 x X0
       have i₂ := eq54 X0 sF1 x sF1
       grind)
    | exact superpose eq54 eq231315
    | exact resolve eq231315 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231315
  have eq246185 : ∀ X0 X1 : G, (σ (M.op (τ X0) y)) = (k X0 (σ (M.op y X1))) ∨ (M.op (M.op x y) X1) = (M.op (τ X0) y) := by
    intro X0 X1
    first
    | exact superpose eq223094 eq6338
    | (have j0 := eq6338 X0 X1
       grind)
    | exact resolve eq6338 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6338
  have eq246186 : ∀ X0 X1 : G, (σ (M.op (τ X0) y)) = (k X0 (σ (M.op y X1))) ∨ (M.op y X1) = (M.op (τ X0) y) := by
    intro X0 X1
    first
    | exact superpose eq223094 eq246185
    | (have j0 := eq246185 X0 X1
       grind)
    | exact resolve eq246185 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246185
  have eq246390 : ∀ X0 : G, (σ (k x (M.op y X0))) = (σ (M.op (τ (σ x)) y)) ∨ (M.op y X0) = (M.op (τ (σ x)) y) := by
    intro X0
    first
    | (have i₁ := eq35 (M.op y x)
       have i₂ := eq246186 sF2 x
       grind)
    | exact superpose eq246186 eq35
    | (have j1 := eq246186 (σ x) X0
       grind)
    | exact resolve eq35 eq246186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246186
  have eq246653 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x (M.op y X0))) ∨ (M.op y X0) = (M.op (τ (σ x)) y) := by
    intro X0
    first
    | exact superpose eq28 eq246390
    | (have j0 := eq246390 X0
       grind)
    | exact resolve eq246390 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246390
  have eq246773 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x (M.op y X0))) ∨ (M.op y X0) = (M.op (τ (σ x)) y) := by
    intro X0
    first
    | (have i₁ := eq246653 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq246653
    | (have j0 := eq246653 X0
       grind)
    | exact resolve eq246653 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246653
  have eq246872 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x (M.op y X0))) ∨ (M.op y X0) = (M.op (τ (σ x)) y) := by
    intro X0
    first
    | exact superpose eq20 eq246773
    | (have j0 := eq246773 X0
       grind)
    | exact resolve eq246773 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246773
  have eq246924 : ∀ X0 : G, (M.op x y) = (M.op y X0) ∨ (σ (M.op x y)) = (σ (k x (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq28 eq246872
    | (have j0 := eq246872 X0
       grind)
    | exact resolve eq246872 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq246872
  have eq246957 : ∀ X0 : G, (M.op x y) = (M.op y X0) ∨ (σ (M.op x y)) = (σ (k x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq246924 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq246924
    | (have j0 := eq246924 X0
       grind)
    | exact resolve eq246924 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246924
  have eq246965 : ∀ X0 : G, (σ (M.op x y)) = (σ (k x (M.op y X0))) ∨ y = (M.op y X0) := by
    intro X0
    first
    | exact superpose eq223094 eq246957
    | (have j0 := eq246957 X0
       grind)
    | exact resolve eq246957 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246957
  have eq247050 : (σ (M.op x y)) = (k (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq163
       have i₂ := eq246965 y
       grind)
    | exact superpose eq246965 eq163
    | (have j1 := eq246965 y
       grind)
    | exact resolve eq163 eq246965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq247068 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x (M.op y X0)) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (M.op y X0))
       have i₂ := eq246965 X0
       grind)
    | exact superpose eq246965 eq16
    | (have j1 := eq246965 X0
       grind)
    | exact resolve eq16 eq246965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246965
  have eq247267 : ∀ X0 : G, (M.op x y) = (k x (M.op y X0)) ∨ y = (M.op y X0) := by
    intro X0
    first
    | exact superpose eq30 eq247068
    | (have j0 := eq247068 X0
       grind)
    | exact resolve eq247068 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq247068
  have eq247279 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq223375 eq247050
    | exact resolve eq247050 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247050
  have eq247301 : ∀ X0 : G, y = (k x (M.op y X0)) ∨ y = (M.op y X0) := by
    intro X0
    first
    | exact superpose eq223094 eq247267
    | (have j0 := eq247267 X0
       grind)
    | exact resolve eq247267 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247267
  have eq247342 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq247279 eq78
    | (have j0 := eq78 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq78 eq247279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247279
  have eq247358 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq231335 eq247342
    | exact resolve eq247342 eq231335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247342
  have eq247364 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq223407 eq247358
    | exact resolve eq247358 eq223407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247358
  have eq247368 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq247364
       have r₂ := eq27
       grind)
    | exact resolve eq247364 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247364
  have eq247371 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq231335 eq247368
    | exact resolve eq247368 eq231335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247368
  have eq247373 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq223407 eq247371
    | exact resolve eq247371 eq223407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247371
  have eq247378 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq247373 eq200
    | exact resolve eq200 eq247373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq247373
  have eq247483 : (τ (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq223094 eq247378
    | exact resolve eq247378 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247378
  have eq248446 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (τ (M.op (σ x) (σ y))) X1)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq247483
       grind)
    | exact superpose eq247483 eq54
    | exact resolve eq54 eq247483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257418 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq223242
       grind)
    | exact superpose eq223242 eq44
    | exact resolve eq44 eq223242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257482 : (k (σ x) (σ (M.op x y))) = (σ (M.op y x)) ∨ (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq223375 eq257418
    | exact resolve eq257418 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257418
  have eq282152 : ∀ X0 X1 : G, (k (k X0 (σ X1)) (σ (M.op x y))) = (σ (M.op (k (τ X0) X1) y)) ∨ y = (M.op (k (τ X0) X1) y) := by
    intro X0 X1
    first
    | exact superpose eq223375 eq2873
    | (have j0 := eq2873 X0 X1
       grind)
    | exact resolve eq2873 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873
  have eq282460 : ∀ X0 : G, (k (k X0 (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (τ (k X0 (σ (M.op x y)))) y)) ∨ y = (M.op (τ (k X0 (σ (M.op x y)))) y) := by
    intro X0
    first
    | exact superpose eq1492 eq282152
    | exact resolve eq282152 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492 eq282152
  have eq282680 : ∀ X0 : G, (k (k X0 (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (τ (k X0 (σ (M.op x y)))) y)) ∨ y = (M.op (τ (k X0 (σ (M.op x y)))) y) := by
    intro X0
    first
    | exact superpose eq20 eq282460
    | (have j0 := eq282460 X0
       grind)
    | exact resolve eq282460 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282460
  have eq303582 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq223429 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq223429
    | (have j0 := eq223429 x
       grind)
    | exact resolve eq223429 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223429
  have eq303639 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq223407 eq303582
    | exact resolve eq303582 eq223407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303582
  have eq303838 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq303639
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq303639
    | exact resolve eq303639 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303639
  have eq303981 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq223375 eq303838
    | exact resolve eq303838 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303838
  have eq304054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq223407 eq303981
    | exact resolve eq303981 eq223407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303981
  have eq304099 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq304054
       have r₂ := eq27
       grind)
    | exact resolve eq304054 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304054
  have eq304208 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq304099 eq62
    | exact resolve eq62 eq304099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304216 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq304099 eq229974
    | exact resolve eq229974 eq304099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229974
  have eq304231 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq223094 eq304208
    | exact resolve eq304208 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304208
  have eq304234 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq304231
       have i₂ := eq223242
       grind)
    | exact superpose eq223242 eq304231
    | exact resolve eq304231 eq223242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223242
  have eq305530 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq304234
       have i₂ := eq247483
       grind)
    | exact superpose eq247483 eq304234
    | exact resolve eq304234 eq247483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247483
  have eq305647 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq304234
       grind)
    | exact superpose eq304234 eq54
    | exact resolve eq54 eq304234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304234
  have eq305673 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by grind
  clear eq305530
  have eq305675 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq305647 X0 x
       have i₂ := eq54 x x X0 y
       grind)
    | exact superpose eq54 eq305647
    | exact resolve eq305647 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305647
  have eq306081 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (τ (M.op (σ x) (σ y))) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq305673
       grind)
    | exact superpose eq305673 eq14
    | exact resolve eq14 eq305673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305673
  have eq306383 : (M.op x y) = (M.op x x) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18
       have i₂ := eq305675 x
       grind)
    | exact superpose eq305675 eq18
    | (have j1 := eq305675 x
       grind)
    | exact resolve eq18 eq305675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305675
  have eq306632 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq223094 eq306383
    | exact resolve eq306383 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306383
  have eq306965 : (k (σ (M.op x y)) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq223118
       have i₂ := eq306632
       grind)
    | exact superpose eq306632 eq223118
    | exact resolve eq223118 eq306632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223118
  have eq306969 : (M.op x y) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq223098 x
       have i₂ := eq306632
       grind)
    | exact superpose eq306632 eq223098
    | exact resolve eq223098 eq306632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223098
  have eq306973 : ∀ X0 : G, (M.op (τ (M.op (σ x) (σ y))) y) = (k (τ (M.op (σ x) (σ y))) (M.op y X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq231111 X0 x
       have i₂ := eq306632
       grind)
    | exact superpose eq306632 eq231111
    | exact resolve eq231111 eq306632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306977 : y = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq247301 x
       have i₂ := eq306632
       grind)
    | exact superpose eq306632 eq247301
    | exact resolve eq247301 eq306632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247301 eq306632
  have eq307000 : y = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq306977
       have i₂ := eq1704 sF4
       grind)
    | exact superpose eq1704 eq306977
    | exact resolve eq306977 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704 eq306977
  have eq307004 : (M.op x y) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq306969
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq306969
    | exact resolve eq306969 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306969
  have eq307006 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq306965
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq306965
    | exact resolve eq306965 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306965
  have eq307015 : y = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq223094 eq307004
    | exact resolve eq307004 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307004
  have eq312247 : (M.op y x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | exact superpose eq304099 eq257482
    | exact resolve eq257482 eq304099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257482
  have eq312867 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq312247
       grind)
    | exact superpose eq312247 eq54
    | exact resolve eq54 eq312247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312247
  have eq312895 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq312867 X0 x
       have i₂ := eq54 x x X0 y
       grind)
    | exact superpose eq54 eq312867
    | exact resolve eq312867 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312867
  have eq313096 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq312895 x
       grind)
    | exact superpose eq312895 eq18
    | (have j1 := eq312895 x
       grind)
    | exact resolve eq18 eq312895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312895
  have eq313344 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq223094 eq313096
    | exact resolve eq313096 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313096
  have eq313450 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op y x) (M.op y x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74 (M.op y x)
       have i₂ := eq313344
       grind)
    | exact superpose eq313344 eq74
    | exact resolve eq74 eq313344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq313468 : (σ (k (M.op y x) (M.op (M.op x y) (M.op x y)))) = (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq199 (M.op y x)
       have i₂ := eq313344
       grind)
    | exact superpose eq313344 eq199
    | exact resolve eq199 eq313344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq313344
  have eq313650 : (σ (k (M.op y x) (M.op y y))) = (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq223094 eq313468
    | exact resolve eq313468 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313468
  have eq313664 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op y x) y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq313450
       have i₂ := eq223146 (M.op y x) x
       grind)
    | exact superpose eq223146 eq313450
    | exact resolve eq313450 eq223146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223146 eq313450
  have eq313684 : (σ (M.op (M.op y x) y)) = (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq313650
       have i₂ := eq231111 y x
       grind)
    | exact superpose eq231111 eq313650
    | exact resolve eq313650 eq231111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231111 eq313650
  have eq320605 : (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (σ (k x (M.op (M.op y x) y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35 (M.op (M.op y x) y)
       have i₂ := eq313664
       grind)
    | exact superpose eq313664 eq35
    | exact resolve eq35 eq313664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320618 : (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (σ (k x (M.op (M.op y x) y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85 (M.op (M.op y x) y)
       have i₂ := eq313664
       grind)
    | exact superpose eq313664 eq85
    | exact resolve eq85 eq313664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq313664
  have eq320839 : (σ (M.op x x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq320618
       have i₂ := eq8960 x y y
       grind)
    | exact superpose eq8960 eq320618
    | exact resolve eq320618 eq8960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320618
  have eq320851 : (σ (M.op x x)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq320605
       have i₂ := eq8960 x y y
       grind)
    | exact superpose eq8960 eq320605
    | exact resolve eq320605 eq8960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320605
  have eq320884 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq271 eq320839
    | exact resolve eq320839 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320839
  have eq320895 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq320851
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq320851
    | exact resolve eq320851 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320851
  have eq320920 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq320884
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq320884
    | exact resolve eq320884 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320884
  have eq320950 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq320920
    | exact resolve eq320920 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320920
  have eq320966 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq271 eq320950
    | exact resolve eq320950 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320950
  have eq320970 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq320966
    | exact resolve eq320966 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq320966
  have eq326055 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq320970 eq320895
    | exact resolve eq320895 eq320970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320895
  have eq326058 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq320970 eq271
    | exact resolve eq271 eq320970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326126 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq326055
  have eq326138 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq223375 eq326058
    | exact resolve eq326058 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326058
  have eq329667 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq306081 eq248446
    | exact resolve eq248446 eq306081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248446 eq306081
  have eq329869 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq329667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329667
  have eq330093 : (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq329869 x
       grind)
    | exact superpose eq329869 eq18
    | (have j1 := eq329869 x
       grind)
    | exact resolve eq18 eq329869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq329869
  have eq330366 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq223094 eq330093
    | exact resolve eq330093 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330093
  have eq331773 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq131
       have i₂ := eq330366
       grind)
    | exact superpose eq330366 eq131
    | exact resolve eq131 eq330366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq330366
  have eq331946 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq223375 eq331773
    | exact resolve eq331773 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331773
  have eq331965 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq331946
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq331946
    | exact resolve eq331946 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331946
  have eq331981 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq223375 eq331965
    | exact resolve eq331965 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331965
  have eq558435 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (σ (k (k X0 X1) y))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op x y)) = (M.op (σ (k X0 X1)) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq223094 eq7603
    | (have j0 := eq7603 X0 X1 X2
       grind)
    | exact resolve eq7603 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7603
  have eq560435 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (k (σ x) (σ (M.op x y))) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq211 eq558435
    | (have j0 := eq558435 x (M.op x y) x
       grind)
    | exact resolve eq558435 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq558435
  have eq560838 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (k (σ x) (σ (M.op x y))) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq223375 eq560435
    | exact resolve eq560435 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560435
  have eq561023 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq304099 eq560838
    | exact resolve eq560838 eq304099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560838
  have eq561192 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq561023
    | (have j0 := eq561023 X0
       grind)
    | exact resolve eq561023 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561023
  have eq561325 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op X0 (σ (M.op x y))) = (M.op X0 (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq561192
    | (have j0 := eq561192 X0
       grind)
    | exact resolve eq561192 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq561192
  have eq561446 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op X0 (σ (M.op x y))) = (M.op X0 (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq561325 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq561325
    | (have j0 := eq561325 X0
       grind)
    | exact resolve eq561325 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561325
  have eq561549 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ (M.op x y))) = (M.op X0 (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq223407 eq561446
    | (have j0 := eq561446 X0
       grind)
    | exact resolve eq561446 eq223407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561446
  have eq561636 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (k x (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq561549 X0
       grind)
    | (have r₁ := eq561549 X0
       have r₂ := eq27
       grind)
    | exact resolve eq561549 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561549
  have eq561710 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op X0 (σ (M.op x y))) = (M.op X0 (k (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq45 eq561636
    | (have j0 := eq561636 X0
       grind)
    | exact resolve eq561636 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq561636
  have eq561752 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq304099 eq561710
    | (have j0 := eq561710 X0
       grind)
    | exact resolve eq561710 eq304099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561710
  have eq592587 : (M.op (τ (M.op (σ x) (σ y))) y) = (τ (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq306973 eq1478
    | exact resolve eq1478 eq306973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478 eq306973
  have eq592842 : (M.op (τ (M.op (σ x) (σ y))) y) = (τ (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq223375 eq592587
    | exact resolve eq592587 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592587
  have eq691209 : (σ (M.op (τ (M.op (σ x) (σ y))) y)) = (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq592842 eq15
    | exact resolve eq15 eq592842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592842
  have eq1508206 : (σ (k x (M.op (M.op y x) y))) = (k (σ x) (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35 (M.op (M.op y x) y)
       have i₂ := eq313684
       grind)
    | exact superpose eq313684 eq35
    | exact resolve eq35 eq313684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313684
  have eq1508644 : (σ (M.op x x)) = (k (σ x) (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1508206
       have i₂ := eq8960 x y y
       grind)
    | exact superpose eq8960 eq1508206
    | exact resolve eq1508206 eq8960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8960 eq1508206
  have eq1508688 : (M.op (σ x) (σ x)) = (k (σ x) (k (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1508644
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq1508644
    | exact resolve eq1508644 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508644
  have eq1508752 : (M.op (σ x) (σ x)) = (k (σ x) (σ (M.op (τ (M.op (σ x) (σ y))) y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq691209 eq1508688
    | exact resolve eq1508688 eq691209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691209 eq1508688
  have eq1508810 : (M.op (σ x) (σ x)) = (k (σ x) (σ (M.op (τ (M.op (σ x) (σ y))) y))) ∨ y = (M.op x x) := by grind
  clear eq1508752
  have eq1508826 : (M.op (σ x) (σ x)) = (σ (k x (M.op (τ (M.op (σ x) (σ y))) y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq35 eq1508810
    | exact resolve eq1508810 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1508810
  have eq1761526 : y = (τ (M.op (σ x) (σ x))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq326126 eq307000
    | exact resolve eq307000 eq326126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307000 eq326126
  have eq1761706 : y = (τ (M.op (σ x) (σ x))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1761526
  have eq1761732 : y = (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq72 eq1761706
    | exact resolve eq1761706 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1761706
  have eq1761733 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq1761732
  have eq1765743 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq326138 eq320970
    | exact resolve eq320970 eq326138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320970 eq326138
  have eq1765854 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1765743
  have eq2032884 : (k (k (σ x) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (k x (M.op x y)) y)) ∨ y = (M.op (k x (M.op x y)) y) := by
    first
    | exact superpose eq62 eq282680
    | exact resolve eq282680 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq282680
  have eq2033363 : (k (k (σ x) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (k x y) y)) ∨ y = (M.op (k x (M.op x y)) y) := by
    first
    | exact superpose eq223094 eq2032884
    | exact resolve eq2032884 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032884
  have eq2033423 : (k (k (σ x) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (τ (M.op (σ x) (σ y))) y)) ∨ y = (M.op (k x (M.op x y)) y) := by
    first
    | (have i₁ := eq2033363
       have i₂ := eq304231
       grind)
    | exact superpose eq304231 eq2033363
    | exact resolve eq2033363 eq304231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033363
  have eq2033461 : (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (M.op (τ (M.op (σ x) (σ y))) y)) ∨ y = (M.op (k x (M.op x y)) y) := by
    first
    | exact superpose eq304099 eq2033423
    | exact resolve eq2033423 eq304099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033423
  have eq2033484 : y = (M.op (k x y) y) ∨ (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (M.op (τ (M.op (σ x) (σ y))) y)) := by
    first
    | exact superpose eq223094 eq2033461
    | exact resolve eq2033461 eq223094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223094 eq2033461
  have eq2033496 : (k (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (M.op (τ (M.op (σ x) (σ y))) y)) ∨ y = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | (have i₁ := eq2033484
       have i₂ := eq304231
       grind)
    | exact superpose eq304231 eq2033484
    | exact resolve eq2033484 eq304231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304231 eq2033484
  have eq2033582 : (M.op (τ (M.op (σ x) (σ y))) y) = (τ (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq2033496 eq16
    | exact resolve eq16 eq2033496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033496
  have eq2034271 : y ≠ (τ (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) y) := by grind
  clear eq2033582
  have eq2034534 : y ≠ (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2034271
       have i₂ := eq78 sF4 sF1
       grind)
    | exact superpose eq78 eq2034271
    | (have j1 := eq78 (τ (M.op (σ x) (σ y))) y
       grind)
    | exact resolve eq2034271 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq2034271
  have eq2038405 : y ≠ (τ (M.op (σ x) (σ y))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1765854 eq2034534
    | exact resolve eq2034534 eq1765854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765854 eq2034534
  have eq2038417 : y = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2038405
       have r₂ := eq1761733
       grind)
    | exact resolve eq2038405 eq1761733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761733 eq2038405
  have eq2038418 : y = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2038417
       have r₂ := eq27
       grind)
    | exact resolve eq2038417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038417
  have eq2038474 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2038418 eq1508826
    | exact resolve eq1508826 eq2038418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508826 eq2038418
  have eq2038572 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq2038474
  have eq2038592 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2038572
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq2038572
    | exact resolve eq2038572 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2038572
  have eq2038603 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq223375 eq2038592
    | exact resolve eq2038592 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038592
  have eq2038612 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq304099 eq2038603
    | exact resolve eq2038603 eq304099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038603
  have eq2038613 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2038612
  have eq2038684 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2038613 eq304216
    | (have r₁ := eq304216
       have r₂ := eq2038613
       grind)
    | exact resolve eq304216 eq2038613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304216
  have eq2038712 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (σ x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq2038613 eq54
    | exact resolve eq54 eq2038613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2038613
  have eq2038768 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2038684
  have eq2038788 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq271 eq2038712
    | exact resolve eq2038712 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq2038712
  have eq2038796 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq223375 eq2038788
    | exact resolve eq2038788 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038788
  have eq2040343 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2038768 eq307006
    | exact resolve eq307006 eq2038768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307006 eq2038768
  have eq2040426 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq2040343
  have eq2045922 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2040426 eq2038796
    | exact resolve eq2038796 eq2040426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038796 eq2040426
  have eq2045973 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2045922
  have eq2048320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2045973 eq331981
    | exact resolve eq331981 eq2045973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331981 eq2045973
  have eq2048671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2048320
  have eq2048719 : y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq2048671
       have r₂ := eq27
       grind)
    | exact resolve eq2048671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048671
  have eq2048754 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq2048719
       grind)
    | exact superpose eq2048719 eq73
    | exact resolve eq73 eq2048719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2048797 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1382 x X0 X1
       have i₂ := eq2048719
       grind)
    | exact superpose eq2048719 eq1382
    | exact resolve eq1382 eq2048719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382 eq2048719
  have eq2048895 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op X0 (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2048797 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2048797
    | (have j0 := eq2048797 X0 X1
       grind)
    | exact resolve eq2048797 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048797
  have eq2048917 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2048754
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2048754
    | exact resolve eq2048754 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048754
  have eq2048940 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op X0 (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2048895 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2048895
    | (have j0 := eq2048895 X0 X1
       grind)
    | exact resolve eq2048895 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048895
  have eq2048956 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq223375 eq2048917
    | exact resolve eq2048917 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048917
  have eq2048970 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq223375 eq2048940
    | exact resolve eq2048940 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048940
  have eq2079293 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq231335 eq2048970
    | exact resolve eq2048970 eq231335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231335 eq2048970
  have eq2080906 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2079293 eq2048956
    | exact resolve eq2048956 eq2079293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048956 eq2079293
  have eq2081056 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2080906
  have eq2081078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq223407 eq2081056
    | exact resolve eq2081056 eq223407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081056
  have eq2081129 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq2081078
       have r₂ := eq27
       grind)
    | exact resolve eq2081078 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081078
  have eq2081186 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2081129 eq307015
    | exact resolve eq307015 eq2081129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307015
  have eq2081302 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2081129 eq15
    | exact resolve eq15 eq2081129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081129
  have eq2081804 : y = (M.op x x) := by grind
  clear eq2081186
  have eq2081970 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2081302
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2081302
    | exact resolve eq2081302 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2081302
  have eq2082783 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2081970 eq561752
    | exact resolve eq561752 eq2081970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561752
  have eq2083650 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq304099 eq2082783
    | exact resolve eq2082783 eq304099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304099 eq2082783
  have eq2084148 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2081970 eq2083650
    | exact resolve eq2083650 eq2081970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081970 eq2083650
  have eq2084401 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq223407 eq2084148
    | (have j0 := eq2084148 X0
       grind)
    | exact resolve eq2084148 eq223407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084148
  have eq2084531 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq2084401 X0
       grind)
    | (have r₁ := eq2084401 X0
       have r₂ := eq27
       grind)
    | exact resolve eq2084401 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084401
  have eq2084660 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq2081804
       grind)
    | exact superpose eq2081804 eq73
    | exact resolve eq73 eq2081804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2081804
  have eq2084828 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2084660
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2084660
    | exact resolve eq2084660 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2084660
  have eq2084874 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq223375 eq2084828
    | exact resolve eq2084828 eq223375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223375 eq2084828
  have eq2085888 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2084531 eq2084874
    | exact resolve eq2084874 eq2084531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084531 eq2084874
  have eq2086050 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq223407 eq2085888
    | exact resolve eq2085888 eq223407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223407 eq2085888
  have eq2086239 : False := by grind
  exact eq2086239

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
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
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
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
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq93
    | exact resolve eq93 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq95
    | exact resolve eq95 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq103 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq86
    | (have j0 := eq86 (σ X0) (σ X1)
       grind)
    | exact resolve eq86 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq44
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq44 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq120 : (k x (M.op x y)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq62
       have i₂ := eq86 sF2 sF1
       grind)
    | exact superpose eq86 eq62
    | (have j1 := eq86 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq62 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq128 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq125
    | exact resolve eq125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq128
    | exact resolve eq128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq130 : (σ (k y (M.op y y))) = (k (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq36
    | exact resolve eq36 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq134 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq149 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq149
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq149
    | exact resolve eq149 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq154 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq67 sF0
       grind)
    | exact superpose eq67 eq152
    | exact resolve eq152 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq169 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq148 eq16
    | exact resolve eq16 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq175 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq154 eq16
    | exact resolve eq16 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq86
    | (have j0 := eq86 (σ x) (σ y)
       grind)
    | exact resolve eq86 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq196
    | exact resolve eq196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq200 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq197
       have r₂ := eq27
       grind)
    | exact resolve eq197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq202 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq200
    | exact resolve eq200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq268 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq271 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 x X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq268
    | exact resolve eq268 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq315 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq34
    | exact resolve eq34 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq326 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq315
    | exact resolve eq315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq328 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq326 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq326
    | exact resolve eq326 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq354 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq426 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 (M.op (M.op X0 X1) X2)) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op (M.op X0 X1) X2)
       have i₂ := eq54 X2 X1 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X3 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq54 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq13 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq54 X0 X1 X1 X3
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 X1) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq426 X0 X1 X2 X3
       have i₂ := eq54 X2 X1 X3 X0
       grind)
    | exact superpose eq54 eq426
    | (have j0 := eq426 X0 X1 X2 X3
       grind)
    | (have r₁ := eq426 X0 X1 X2 (M.op (M.op X3 X1) X0)
       have r₂ := eq54 X0 X1 (M.op (M.op X0 X1) X2) X3
       grind)
    | (have r₁ := eq426 X0 (M.op (M.op X3 X1) X0) X2 X1
       have r₂ := eq54 X0 X1 (M.op (M.op X0 (M.op (M.op X3 X1) X0)) X2) X3
       grind)
    | exact resolve eq426 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq494 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq79
    | (have r₁ := eq79
       have r₂ := eq202
       grind)
    | exact resolve eq79 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq495 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq494
  have eq496 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq495 eq134
    | exact resolve eq134 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X0)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq495 eq14
    | exact resolve eq14 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq506 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq501 X0
       have i₂ := eq14 X0 sF2 sF3
       grind)
    | exact superpose eq14 eq501
    | exact resolve eq501 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq509 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq506
    | (have j0 := eq506 (σ x)
       grind)
    | exact resolve eq506 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq539 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq509 eq65
    | (have r₁ := eq65
       have r₂ := eq509
       grind)
    | exact resolve eq65 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq540 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq509 eq72
    | exact resolve eq72 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq539
  have eq582 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op (σ (k X0 X1)) X3)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X3 (σ X1) X2 (σ X0)
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq54
    | (have j1 := eq109 X0 X1
       grind)
    | exact resolve eq54 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq109 X0 X1
       grind)
    | exact resolve eq13 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq587 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq584
    | (have j0 := eq584 X0 X1
       grind)
    | exact resolve eq584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq602 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (τ (M.op (σ x) (σ y))) X1)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 x X0 x
       have i₂ := eq540
       grind)
    | exact superpose eq540 eq54
    | exact resolve eq54 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq608 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq546 eq103
    | exact resolve eq103 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq546
  have eq654 : (k y x) = (M.op y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq608 eq496
    | exact resolve eq496 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq608
  have eq658 : (k y x) = (M.op y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq654
  have eq661 : (M.op y x) = (M.op y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq658
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq658
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq658 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq976 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (τ (σ y)) X1)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq202 eq602
    | exact resolve eq602 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq1028 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (τ (σ y)) X1)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq976 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1031 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq1028
    | exact resolve eq1028 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1028
  have eq1226 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ (M.op (M.op (σ x) (σ y)) X1) ∨ (M.op (M.op (M.op (σ x) (σ y)) X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op (M.op (σ x) (σ y)) X1)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq271 eq12
    | (have j0 := eq12 X0 (M.op (M.op (σ x) (σ y)) X1)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq271 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1245 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ (M.op (M.op (σ x) (σ y)) X1) ∨ (M.op (M.op (M.op (σ x) (σ y)) X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) X1) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq271 eq1226
    | (have j0 := eq1226 X0 X1
       grind)
    | (have r₁ := eq1226 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)
       have r₂ := eq271 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1226 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq1226
  have eq1339 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X0)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq661
       grind)
    | exact superpose eq661 eq14
    | exact resolve eq14 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq1343 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1339 X0
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq1339
    | exact resolve eq1339 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1346 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1343 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1343
    | (have j0 := eq1343 x
       grind)
    | exact resolve eq1343 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1394 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1346 eq129
    | exact resolve eq129 eq1346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1397 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq1394
  have eq1426 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (σ X0) X1 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq54
    | exact resolve eq54 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1438 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1397
       grind)
    | exact superpose eq1397 eq73
    | exact resolve eq73 eq1397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1454 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq1438
    | exact resolve eq1438 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1454 eq509
    | exact resolve eq509 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq1456
  have eq1474 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1470
       have r₂ := eq27
       grind)
    | exact resolve eq1470 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1478 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1474 eq129
    | exact resolve eq129 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1481 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1478
  have eq1490 : x ≠ x ∨ (M.op x y) = (M.op x x) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1481
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1481
       grind)
    | exact resolve eq12 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1492 : (M.op x y) = (M.op x x) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1490
  have eq1493 : (M.op x y) = (M.op x x) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1492
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1492
    | exact resolve eq1492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq1497 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq319 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq319
    | exact resolve eq319 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1507 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq319 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq319
    | (have j0 := eq319 X0 x
       grind)
    | exact resolve eq319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1710 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq354 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq354
    | (have j0 := eq354 y X0
       grind)
    | exact resolve eq354 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1711 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq20 eq354
    | (have j0 := eq354 (M.op x y) X0
       grind)
    | exact resolve eq354 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq1738 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1493
       grind)
    | exact superpose eq1493 eq73
    | exact resolve eq73 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1756 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq1738
    | exact resolve eq1738 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1756 eq509
    | exact resolve eq509 eq1756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1756
  have eq1772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1758
  have eq1776 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1772
       have r₂ := eq27
       grind)
    | exact resolve eq1772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq1780 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1776 eq129
    | exact resolve eq129 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq1783 : y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1780
  have eq1792 : y = (M.op y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq658
       have i₂ := eq1783
       grind)
    | exact superpose eq1783 eq658
    | exact resolve eq658 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq1783
  have eq1795 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1792
  have eq1812 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1795 eq129
    | exact resolve eq129 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1815 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1812
  have eq1832 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq1815
       grind)
    | exact superpose eq1815 eq54
    | exact resolve eq54 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq1871 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1832 X0 x
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq1832
    | exact resolve eq1832 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481 eq1832
  have eq1953 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1871 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq1957 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1953 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1953
    | (have j0 := eq1953 x
       grind)
    | exact resolve eq1953 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq2014 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1957
       grind)
    | exact superpose eq1957 eq73
    | exact resolve eq73 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2032 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq2014
    | exact resolve eq2014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2268 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2032 eq509
    | exact resolve eq509 eq2032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq2282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2268
  have eq2286 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2282
       have r₂ := eq27
       grind)
    | exact resolve eq2282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq2356 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2286 eq129
    | exact resolve eq129 eq2286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq2358 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq2356
  have eq2365 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2358 eq26
    | exact resolve eq26 eq2358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2366 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2358 eq28
    | exact resolve eq28 eq2358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2367 : ∀ X0 : G, (σ (k x X0)) = (k (σ (M.op x y)) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2358 eq35
    | exact resolve eq35 eq2358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2371 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2358 eq62
    | exact resolve eq62 eq2358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2375 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2358 eq129
    | exact resolve eq129 eq2358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq2358
  have eq2417 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2375
  have eq2421 : (k x (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2371
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq2371
    | exact resolve eq2371 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2425 : ∀ X0 : G, (σ (k x X0)) = (σ (k (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq2367
    | exact resolve eq2367 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2367
  have eq2426 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2366
    | exact resolve eq2366 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2428 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq175 eq2421
    | exact resolve eq2421 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq2484 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2426
  have eq2610 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2417 eq169
    | exact resolve eq169 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq2417
  have eq2612 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq2610
    | exact resolve eq2610 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2610
  have eq4333 : (σ (M.op x y)) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2428 eq586
    | (have j0 := eq586 x (M.op x y)
       grind)
    | exact resolve eq586 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428
  have eq4410 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq154 eq4333
    | exact resolve eq4333 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333
  have eq4445 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq4410
    | exact resolve eq4410 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4410
  have eq4477 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq4445
    | exact resolve eq4445 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq4490 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4477
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4477
    | exact resolve eq4477 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4477
  have eq4933 : ∀ X0 : G, (k (M.op x y) X0) = (τ (σ (k x X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2425 eq16
    | exact resolve eq16 eq2425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425
  have eq4980 : ∀ X0 : G, (k x X0) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4933 X0
       have i₂ := eq16 (k x X0)
       grind)
    | exact superpose eq16 eq4933
    | exact resolve eq4933 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq5091 : ∀ X0 : G, (k (τ (M.op x y)) X0) = (τ (k x (σ X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4980 eq319
    | exact resolve eq319 eq4980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4980
  have eq5133 : ∀ X0 : G, (k (τ (M.op x y)) X0) = (k (τ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5091 X0
       have i₂ := eq319 x X0
       grind)
    | exact superpose eq319 eq5091
    | exact resolve eq5091 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq5091
  have eq9022 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq432 X1 X0 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq10504 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq587
    | (have j0 := eq587 X0 X1
       grind)
    | exact resolve eq587 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq14042 : ∀ X0 : G, (σ x) ≠ (σ (τ (k X0 (σ x)))) ∨ (σ x) = (M.op (σ (τ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq586 (τ X0) x
       have i₂ := eq1507 X0
       grind)
    | exact superpose eq1507 eq586
    | (have j0 := eq586 (τ X0) x
       grind)
    | exact resolve eq586 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507
  have eq14047 : ∀ X0 : G, (σ x) ≠ (k X0 (σ x)) ∨ (σ x) = (M.op (σ (τ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14042 X0
       have i₂ := eq15 (k X0 sF2)
       grind)
    | exact superpose eq15 eq14042
    | (have j0 := eq14042 X0
       grind)
    | exact resolve eq14042 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14042
  have eq14064 : ∀ X0 : G, (σ x) ≠ (k X0 (σ x)) ∨ (σ x) = (M.op (σ (τ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14047 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14047
    | (have j0 := eq14047 X0
       grind)
    | exact resolve eq14047 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14047
  have eq14073 : ∀ X0 : G, (σ x) = (M.op (σ (τ X0)) (σ x)) ∨ (σ x) ≠ (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14064 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14064
    | (have j0 := eq14064 X0
       grind)
    | exact resolve eq14064 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14064
  have eq14077 : ∀ X0 : G, (σ x) ≠ (k X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14073 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14073
    | (have j0 := eq14073 X0
       grind)
    | exact resolve eq14073 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14073
  have eq14815 : (k y (M.op y y)) = (τ (k (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq134 eq1710
    | exact resolve eq1710 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq15047 : (k (M.op x y) (k x x)) = (τ (k (σ (M.op x y)) (k (σ x) (σ x)))) := by
    first
    | exact superpose eq49 eq1711
    | exact resolve eq1711 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1711
  have eq15107 : (k (M.op x y) (k x x)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq15047
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq15047
    | exact resolve eq15047 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15047
  have eq15131 : (k (M.op x y) (M.op x x)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq15107
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq15107
    | exact resolve eq15107 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq15107
  have eq15550 : ∀ X0 : G, (k (τ x) (τ X0)) = (τ (k (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5133 (τ X0)
       have i₂ := eq1497 X0 sF0
       grind)
    | exact superpose eq1497 eq5133
    | exact resolve eq5133 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5133
  have eq15560 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (M.op (σ (τ (k X0 X1))) X3)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq582 (τ X0) (τ X1) X2 X3
       have i₂ := eq1497 X1 X0
       grind)
    | exact superpose eq1497 eq582
    | (have j0 := eq582 (τ X0) (τ X1) X2 X3
       grind)
    | exact resolve eq582 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq15561 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq586 (τ X0) (τ X1)
       have i₂ := eq1497 X1 X0
       grind)
    | exact superpose eq1497 eq586
    | (have j0 := eq586 (τ X0) (τ X1)
       grind)
    | exact resolve eq586 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq15564 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10504 (τ X0) (τ X1)
       have i₂ := eq1497 X1 X0
       grind)
    | exact superpose eq1497 eq10504
    | (have j0 := eq10504 (τ X0) (τ X1)
       grind)
    | exact resolve eq10504 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10504
  have eq15567 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15564 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq15564
    | (have j0 := eq15564 X0 X1
       grind)
    | exact resolve eq15564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15564
  have eq15570 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15561 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq15561
    | (have j0 := eq15561 X0 X1
       grind)
    | exact resolve eq15561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15561
  have eq15571 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ (τ X1))) = (M.op X2 (M.op (k X0 X1) X3)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15560 X0 X1 X2 X3
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq15560
    | (have j0 := eq15560 X0 X1 X2 X3
       grind)
    | exact resolve eq15560 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15560
  have eq15580 : ∀ X0 : G, (τ (k (M.op x y) X0)) = (τ (k x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15550 X0
       have i₂ := eq1497 X0 x
       grind)
    | exact superpose eq1497 eq15550
    | exact resolve eq15550 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497 eq15550
  have eq15619 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15567 X0 X1
       have i₂ := eq328 X0
       grind)
    | exact superpose eq328 eq15567
    | (have j0 := eq15567 X0 X1
       grind)
    | exact resolve eq15567 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15567
  have eq15622 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15570 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq15570
    | (have j0 := eq15570 X0 X1
       grind)
    | exact resolve eq15570 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15570
  have eq15623 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (k X0 X1) X3)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15571 X0 X1 X2 X3
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq15571
    | (have j0 := eq15571 X0 X1 X2 X3
       grind)
    | exact resolve eq15571 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15571
  have eq15639 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15619 X0 X1
       have i₂ := eq34 X1 (τ X0)
       grind)
    | exact superpose eq34 eq15619
    | (have j0 := eq15619 X0 X1
       grind)
    | exact resolve eq15619 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq15619
  have eq15642 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15622 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15622
    | (have j0 := eq15622 X0 X1
       grind)
    | exact resolve eq15622 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15622
  have eq15643 : ∀ X0 X1 X2 X3 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X2 X1) = (M.op X2 (M.op (k X0 X1) X3)) := by
    intro X0 X1 X2 X3
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f15643_17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
      intro X0 X1
      grind
    have f15643_19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
      intro X0 X1
      grind
    have f15643_20 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
      intro X0 X1 X2
      grind
    have f15643_21 : ∀ X0 : G, (σ (τ X0)) = X0 := by
      intro X0
      grind
    have f15643_23 : X1 ≠ (M.op (σ (τ X0)) X1) := by grind
    have f15643_24 : (M.op X2 X1) ≠ (M.op X2 (M.op (k X0 X1) X3)) := by grind
    have f15643_25 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
      intro X0 X1
      first
      | (have j0 := f15643_17 X0 X1
         have j1 := f15643_19 X0 X1
         grind)
      | (have r₁ := f15643_17 X0 X1
         have r₂ := f15643_19 X0 X1
         grind)
      | (have r₁ := f15643_17 X0 X0
         have r₂ := f15643_19 X0 X0
         grind)
      | (have r₁ := f15643_17 X1 (M.op X1 X1)
         have r₂ := f15643_19 (M.op X1 X1) X1
         grind)
      | exact resolve f15643_17 f15643_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15643_28 : X1 ≠ (M.op X0 X1) := by
      first
      | (have i₁ := f15643_23
         have i₂ := f15643_21 X0
         grind)
      | exact superpose f15643_21 f15643_23
      | exact resolve f15643_23 f15643_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15643_35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f15643_20 X2 (M.op (M.op X3 X1) X0) X0
         have i₂ := f15643_20 X0 X1 X3
         grind)
      | exact superpose f15643_20 f15643_20
      | exact resolve f15643_20 f15643_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15643_37 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f15643_35 X0 X1 X2 X3
         have i₂ := f15643_20 X2 X1 X0
         grind)
      | exact superpose f15643_20 f15643_35
      | exact resolve f15643_35 f15643_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15643_59 : (M.op X2 X1) ≠ (M.op X2 (M.op (M.op X0 X1) X3)) ∨ X1 = (M.op X0 X1) := by
      first
      | (have i₁ := f15643_24
         have i₂ := f15643_25 X0 X1
         grind)
      | exact superpose f15643_25 f15643_24
      | (have j1 := f15643_25 X0 X1
         grind)
      | exact resolve f15643_24 f15643_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15643_60 : X1 = (M.op X0 X1) := by
      first
      | (have r₁ := f15643_59
         have r₂ := f15643_37 X3 X1 X2 X0
         grind)
      | exact resolve f15643_59 f15643_37
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15643_61 : False := by
      first
      | (have r₁ := f15643_60
         have r₂ := f15643_28
         grind)
      | exact resolve f15643_60 f15643_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f15643_61
  clear eq15623
  have eq15645 : ∀ X0 X1 : G, (k X1 X0) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15639 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15639
    | (have j0 := eq15639 X0 X1
       grind)
    | exact resolve eq15639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15639
  have eq15648 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15642 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15642
    | (have j0 := eq15642 X0 X1
       grind)
    | exact resolve eq15642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15642
  have eq15649 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (k X0 X1) X3)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15643 X0 X1 X2 X3
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15643
    | (have j0 := eq15643 X0 X1 X2 X3
       grind)
    | exact resolve eq15643 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15643
  have eq15651 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15645 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq15645
    | (have j0 := eq15645 X0 X1
       grind)
    | exact resolve eq15645 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15645
  have eq15655 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15651 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15651
    | (have j0 := eq15651 X0 X1
       grind)
    | exact resolve eq15651 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15651
  have eq15658 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15655 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15655
    | (have j0 := eq15655 X0 X1
       grind)
    | exact resolve eq15655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15655
  have eq15891 : (τ (M.op x y)) = (τ (k x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2612 eq15580
    | exact resolve eq15580 eq2612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2612 eq15580
  have eq15943 : (τ (M.op x y)) = (τ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq15891
  have eq16001 : (M.op (k x y) (k x y)) = (σ (M.op (τ (M.op x y)) (τ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq328 (k x y)
       have i₂ := eq15943
       grind)
    | exact superpose eq15943 eq328
    | exact resolve eq328 eq15943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15943
  have eq16033 : (M.op (M.op x y) (M.op x y)) = (M.op (k x y) (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16001
       have i₂ := eq328 sF0
       grind)
    | exact superpose eq328 eq16001
    | exact resolve eq16001 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq16001
  have eq16830 : ∀ X0 : G, (M.op y y) = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq9022 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9022
    | (have j0 := eq9022 y x X0
       grind)
    | exact resolve eq9022 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16844 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2365 eq9022
    | (have j0 := eq9022 (σ y) (σ x) X0
       grind)
    | exact resolve eq9022 eq2365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16855 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq9022
    | (have j0 := eq9022 (σ y) (σ x) X0
       grind)
    | exact resolve eq9022 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9022
  have eq17014 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202 eq16844
    | exact resolve eq16844 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16844
  have eq17083 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17014 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17014
  have eq30214 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1426 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq74 (M.op X0 X0)
       grind)
    | exact superpose eq74 eq1426
    | exact resolve eq1426 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1426
  have eq340375 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op X0 (k x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (k x y) X0 (k x y)
       have i₂ := eq16033
       grind)
    | exact superpose eq16033 eq54
    | exact resolve eq54 eq16033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340396 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq340375 x X0
       have i₂ := eq54 X0 sF0 x sF0
       grind)
    | exact superpose eq54 eq340375
    | exact resolve eq340375 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340375
  have eq341800 : (M.op (M.op x y) (M.op x y)) = (M.op (k x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16033
       have i₂ := eq340396 (k x y)
       grind)
    | exact superpose eq340396 eq16033
    | exact resolve eq16033 eq340396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16033 eq340396
  have eq341877 : (M.op (M.op x y) (M.op x y)) = (M.op (k x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq341800
  have eq374738 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have j0 := eq1245 (M.op (σ x) (σ y)) (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq1302457 : (k y (M.op y y)) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17083 eq14815
    | exact resolve eq14815 eq17083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14815 eq17083
  have eq1302999 : (M.op y y) = (k y (M.op y y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq1302457
    | exact resolve eq1302457 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq1302457
  have eq1303100 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15648 y (M.op y y)
       have i₂ := eq1302999
       grind)
    | exact superpose eq1302999 eq15648
    | (have j0 := eq15648 y (M.op y y)
       grind)
    | (have r₁ := eq15648 y (M.op y y)
       have r₂ := eq1302999
       grind)
    | exact resolve eq15648 eq1302999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302999
  have eq1303101 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op x y) := by grind
  clear eq1303100
  have eq1303498 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = (M.op X0 (M.op (M.op y y) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (M.op y y) X0 y
       have i₂ := eq1303101
       grind)
    | exact superpose eq1303101 eq54
    | exact resolve eq54 eq1303101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303101
  have eq1303557 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1303498 X0 x
       have i₂ := eq54 x y X0 y
       grind)
    | exact superpose eq54 eq1303498
    | exact resolve eq1303498 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303498
  have eq1303576 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1031 X0 y
       have i₂ := eq1303557 X0
       grind)
    | exact superpose eq1303557 eq1031
    | exact resolve eq1031 eq1303557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq1303557
  have eq1304172 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1303576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303576
  have eq2890739 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1304172 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1304172
    | (have j0 := eq1304172 x
       grind)
    | exact resolve eq1304172 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304172
  have eq2891952 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2890739 eq58
    | exact resolve eq58 eq2890739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890739
  have eq2892434 : (M.op x y) = (M.op x x) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq2891952
    | exact resolve eq2891952 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891952
  have eq2899029 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq2892434
       grind)
    | exact superpose eq2892434 eq73
    | exact resolve eq73 eq2892434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892434
  have eq2899384 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2899029
    | exact resolve eq2899029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899029
  have eq2919603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2899384 eq509
    | exact resolve eq509 eq2899384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq2899384
  have eq2919861 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq2919603
  have eq2919928 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq2919861
       have r₂ := eq27
       grind)
    | exact resolve eq2919861 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919861
  have eq2930233 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq2919928 eq58
    | exact resolve eq58 eq2919928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq2919928
  have eq2930715 : x = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq2930233
    | exact resolve eq2930233 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930233
  have eq2930716 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq2930715
  have eq2930899 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq341877
       have i₂ := eq2930716
       grind)
    | exact superpose eq2930716 eq341877
    | exact resolve eq341877 eq2930716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341877
  have eq2931030 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq15649 x y X0 X1
       have i₂ := eq2930716
       grind)
    | exact superpose eq2930716 eq15649
    | (have j0 := eq15649 x y x x
       grind)
    | exact resolve eq15649 eq2930716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15649 eq2930716
  have eq2931050 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2930899
  have eq2931110 : ∀ X0 X1 : G, y = (M.op x y) ∨ (M.op X0 y) = (M.op X0 (M.op x X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2931030 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2931030
    | (have j0 := eq2931030 X0 X1
       grind)
    | exact resolve eq2931030 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931030
  have eq2931111 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq2931110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931110
  have eq2936239 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2931050 eq154
    | exact resolve eq154 eq2931050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq2931050
  have eq2944011 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2931111 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2931111
    | (have j0 := eq2931111 X0 y
       grind)
    | exact resolve eq2931111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931111
  have eq2945645 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2944011 eq2936239
    | exact resolve eq2936239 eq2944011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936239 eq2944011
  have eq2946042 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq2945645
  have eq2946121 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2946042
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2946042
    | exact resolve eq2946042 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946042
  have eq2946193 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2946121
    | exact resolve eq2946121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946121
  have eq2946261 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2946193 eq4490
    | (have r₁ := eq4490
       have r₂ := eq2946193
       grind)
    | exact resolve eq4490 eq2946193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4490
  have eq2946472 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x y)) X0)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2946193 eq14
    | exact resolve eq14 eq2946193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946193
  have eq2946554 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq2946261
  have eq2946555 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq2946554
  have eq3377583 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2365 eq2946472
    | exact resolve eq2946472 eq2365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365 eq2946472
  have eq3378527 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq3377583
  have eq3378591 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq3378527
    | exact resolve eq3378527 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq3378527
  have eq3378668 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq3378591
  have eq3378899 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ (M.op x y))) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3378668 eq54
    | exact resolve eq54 eq3378668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3378668
  have eq3378984 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3378899 x X0
       have i₂ := eq54 X0 sF1 x sF3
       grind)
    | exact superpose eq54 eq3378899
    | exact resolve eq3378899 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3378899
  have eq3379720 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3378984
    | (have j0 := eq3378984 (σ x)
       grind)
    | exact resolve eq3378984 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3378984
  have eq3380950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3379720 eq2946555
    | exact resolve eq2946555 eq3379720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946555 eq3379720
  have eq3381068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3380950
  have eq3381157 : y = (M.op x y) := by
    first
    | (have r₁ := eq3381068
       have r₂ := eq27
       grind)
    | exact resolve eq3381068 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381068
  have eq3381172 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3381157 eq20
    | exact resolve eq20 eq3381157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3381174 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq3381157 eq50
    | exact resolve eq50 eq3381157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq3381176 : y ≠ y ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq3381157 eq78
    | (have r₁ := eq78
       have r₂ := eq3381157
       grind)
    | exact resolve eq78 eq3381157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3381432 : ∀ X0 : G, (M.op y y) = (k y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq3381157 eq16830
    | exact resolve eq16830 eq3381157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16830
  have eq3382438 : (M.op y x) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq3381176
  have eq3383162 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3381172
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3381172
    | exact resolve eq3381172 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381172
  have eq3383367 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3383162 eq26
    | exact resolve eq26 eq3383162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3383640 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq3383162 eq16855
    | exact resolve eq16855 eq3383162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16855
  have eq3385901 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3383367 eq120
    | exact resolve eq120 eq3383367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq3386080 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq3385901
       have r₂ := eq27
       grind)
    | exact resolve eq3385901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385901
  have eq3386087 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3381157 eq3386080
    | exact resolve eq3386080 eq3381157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386080
  have eq3390943 : (σ (M.op y y)) = (k (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq3381432 y
       grind)
    | exact superpose eq3381432 eq130
    | exact resolve eq130 eq3381432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq3381432
  have eq3391176 : (σ (M.op y y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3383162 eq3390943
    | exact resolve eq3390943 eq3383162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390943
  have eq3391273 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq3391176
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq3391176
    | exact resolve eq3391176 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391176
  have eq3391364 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3383162 eq3391273
    | exact resolve eq3391273 eq3383162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391273
  have eq3392243 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3391364 eq15648
    | (have j0 := eq15648 (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | (have r₁ := eq15648 (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq3391364
       grind)
    | exact resolve eq15648 eq3391364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15648 eq3391364
  have eq3392262 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by grind
  clear eq3392243
  have eq3392421 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X0 (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3392262 eq54
    | exact resolve eq54 eq3392262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392262
  have eq3392485 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3392421 x X0
       have i₂ := eq54 X0 sF1 x sF1
       grind)
    | exact superpose eq54 eq3392421
    | exact resolve eq3392421 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392421
  have eq3577158 : (M.op y x) = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3382438
       have i₂ := eq3386087
       grind)
    | exact superpose eq3386087 eq3382438
    | exact resolve eq3382438 eq3386087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382438
  have eq3577412 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 y X0 y
       have i₂ := eq3577158
       grind)
    | exact superpose eq3577158 eq54
    | exact resolve eq54 eq3577158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3577158
  have eq3577486 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3577412 X0 x
       have i₂ := eq54 x x X0 y
       grind)
    | exact superpose eq54 eq3577412
    | exact resolve eq3577412 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq3577412
  have eq3578747 : (M.op x y) = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3577486 x
       grind)
    | exact superpose eq3577486 eq18
    | (have j1 := eq3577486 x
       grind)
    | exact resolve eq18 eq3577486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3577486
  have eq3579500 : y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3381157 eq3578747
    | exact resolve eq3578747 eq3381157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3578747
  have eq3580632 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq3579500
       grind)
    | exact superpose eq3579500 eq73
    | exact resolve eq73 eq3579500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq3580828 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq30214 x x
       have i₂ := eq3579500
       grind)
    | exact superpose eq3579500 eq30214
    | exact resolve eq30214 eq3579500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30214 eq3579500
  have eq3580925 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op X0 (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3580828 X0
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq3580828
    | exact resolve eq3580828 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq3580828
  have eq3581038 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3580632
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3580632
    | exact resolve eq3580632 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3580632
  have eq3581052 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op X0 (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3580925 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3580925
    | (have j0 := eq3580925 X0
       grind)
    | exact resolve eq3580925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3580925
  have eq3581163 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3383162 eq3581038
    | exact resolve eq3581038 eq3383162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3581038
  have eq3581172 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3383162 eq3581052
    | exact resolve eq3581052 eq3383162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3581052
  have eq3581267 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3392485 eq3581172
    | exact resolve eq3581172 eq3392485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392485 eq3581172
  have eq3585078 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3581267 eq3581163
    | exact resolve eq3581163 eq3581267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3581163 eq3581267
  have eq3585152 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq3585078
  have eq3585166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3383367 eq3585152
    | exact resolve eq3585152 eq3383367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383367 eq3585152
  have eq3585306 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq3585166
       have r₂ := eq27
       grind)
    | exact resolve eq3585166 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585166
  have eq3585463 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3585306 eq15
    | exact resolve eq15 eq3585306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3586536 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3585463
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3585463
    | exact resolve eq3585463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585463
  have eq3586949 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq3586536 eq27
    | exact resolve eq27 eq3586536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3587019 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3586536 eq374738
    | exact resolve eq374738 eq3586536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374738
  have eq3587054 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq3586536 eq3383640
    | exact resolve eq3383640 eq3586536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383640
  have eq3587081 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq3587019
    | exact resolve eq3587019 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587019
  have eq3587142 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3586536 eq3587081
    | exact resolve eq3587081 eq3586536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587081
  have eq3587183 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq3587142
    | exact resolve eq3587142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587142
  have eq3587205 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3586536 eq3587183
    | exact resolve eq3587183 eq3586536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587183
  have eq3587220 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq3587205
    | exact resolve eq3587205 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3587205
  have eq3587229 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3586536 eq3587220
    | exact resolve eq3587220 eq3586536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586536 eq3587220
  have eq3587235 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14077 (σ x)
       grind)
    | (have r₁ := eq3587229
       have r₂ := eq14077 (σ x)
       grind)
    | exact resolve eq3587229 eq14077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14077 eq3587229
  have eq3587272 : (τ (σ x)) = (M.op x x) := by
    first
    | exact superpose eq3587235 eq72
    | exact resolve eq72 eq3587235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq3587235
  have eq3587563 : x = (M.op x x) := by
    first
    | exact superpose eq28 eq3587272
    | exact resolve eq3587272 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3587272
  have eq3592178 : (k (M.op x y) (M.op x x)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3587054 eq15131
    | exact resolve eq15131 eq3587054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15131 eq3587054
  have eq3592344 : (k (M.op x y) (M.op x x)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq175 eq3592178
    | exact resolve eq3592178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq3592178
  have eq3592381 : (M.op y y) = (k y (M.op x x)) := by
    first
    | exact superpose eq3381157 eq3592344
    | exact resolve eq3592344 eq3381157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592344
  have eq3592403 : (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq3592381
       have i₂ := eq3587563
       grind)
    | exact superpose eq3587563 eq3592381
    | exact resolve eq3592381 eq3587563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592381
  have eq3592817 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq15658 y x
       have i₂ := eq3592403
       grind)
    | exact superpose eq3592403 eq15658
    | (have j0 := eq15658 y x
       grind)
    | (have r₁ := eq15658 y x
       have r₂ := eq3592403
       grind)
    | exact resolve eq15658 eq3592403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15658 eq3592403
  have eq3592832 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by grind
  clear eq3592817
  have eq3592849 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3592832
       have i₂ := eq3386087
       grind)
    | exact superpose eq3386087 eq3592832
    | exact resolve eq3592832 eq3386087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386087 eq3592832
  have eq3593084 : x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3585306 eq3592849
    | exact resolve eq3592849 eq3585306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585306 eq3592849
  have eq3593312 : x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3593084
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3593084
    | exact resolve eq3593084 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593084
  have eq3593513 : x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3381157 eq3593312
    | exact resolve eq3593312 eq3381157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593312
  have eq3596035 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3381174 x
       have i₂ := eq3593513
       grind)
    | exact superpose eq3593513 eq3381174
    | exact resolve eq3381174 eq3593513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381174 eq3593513
  have eq3596107 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3596035
       have i₂ := eq3587563
       grind)
    | exact superpose eq3587563 eq3596035
    | exact resolve eq3596035 eq3587563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587563 eq3596035
  have eq3596127 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3596107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3596107
    | exact resolve eq3596107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3596107
  have eq3596144 : x = (M.op x y) := by
    first
    | (have r₁ := eq3596127
       have r₂ := eq2484
       grind)
    | exact resolve eq3596127 eq2484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2484 eq3596127
  have eq3596157 : x = y := by
    first
    | exact superpose eq3381157 eq3596144
    | exact resolve eq3596144 eq3381157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381157 eq3596144
  have eq3596195 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3596157
       grind)
    | exact superpose eq3596157 eq24
    | exact resolve eq24 eq3596157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3596157
  have eq3599750 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3383162 eq3596195
    | exact resolve eq3596195 eq3383162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383162 eq3596195
  have eq3601329 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3599750
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3599750
    | exact resolve eq3599750 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3599750
  have eq3602575 : False := by grind
  exact eq3602575

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxx_pyx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 X1 X2 X3
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq182 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 (M.op X0 X1) X1 X2 X0
       have i₂ := eq182 (M.op X0 X1)
       grind)
    | exact superpose eq182 eq178
    | exact resolve eq178 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq901 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq919 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq869 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq928 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq901 X0 X1 X2
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq901
    | (have j0 := eq901 X0 X1 X2
       grind)
    | exact resolve eq901 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq949 : ∀ X0 X1 : G, (k X1 X0) = (k X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq919 X0 X1
       have i₂ := eq182 X1
       grind)
    | exact superpose eq182 eq919
    | (have j0 := eq919 X0 X1
       grind)
    | exact resolve eq919 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq6689 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq928 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq6690 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6689 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq6689
    | (have j0 := eq6689 X0 X1
       grind)
    | (have r₁ := eq6689 X0 X0
       have r₂ := eq182 X0
       grind)
    | exact resolve eq6689 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6689
  have eq6776 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6690 X0 X1
       have j1 := eq949 X1 X0
       grind)
    | (have r₁ := eq6690 X1 X0
       have r₂ := eq949 X0 X1
       grind)
    | (have r₁ := eq6690 X0 X0
       have r₂ := eq949 X0 X0
       grind)
    | exact resolve eq6690 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949 eq6690
  have eq6833 : (M.op x y) = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6776 x y
       grind)
    | exact superpose eq6776 eq18
    | (have j1 := eq6776 x y
       grind)
    | exact resolve eq18 eq6776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6839 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq6776 sF2 sF3
       grind)
    | exact superpose eq6776 eq26
    | (have j1 := eq6776 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq6776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6857 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6833
       grind)
    | exact superpose eq6833 eq40
    | exact resolve eq40 eq6833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6833
  have eq6858 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6857
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6857
    | exact resolve eq6857 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6857
  have eq6862 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq6858
    | exact resolve eq6858 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6858
  have eq6870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6862 eq6839
    | exact resolve eq6839 eq6862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6877 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq6870
       have r₂ := eq27
       grind)
    | exact resolve eq6870 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6870
  have eq6889 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq6877 eq178
    | exact resolve eq178 eq6877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6951 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq6877 eq6889
    | exact resolve eq6889 eq6877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6889
  have eq7008 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq6951 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6951
  have eq7028 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq7008 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq7008 (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7008 (σ y)
       grind)
    | exact resolve eq13 eq7008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7038 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq7008 eq6776
    | (have j0 := eq6776 X0 (σ y)
       grind)
    | exact resolve eq6776 eq7008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7048 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7008 eq26
    | (have j1 := eq7008 (σ x)
       grind)
    | exact resolve eq26 eq7008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7008
  have eq7054 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq7048
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq7048
    | exact resolve eq7048 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7048
  have eq7061 : ∀ X0 : G, (k X0 (σ y)) = (k X0 X0) ∨ (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq7028 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq7028
    | (have j0 := eq7028 X0
       grind)
    | exact resolve eq7028 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7028
  have eq7066 : ∀ X0 : G, (k X0 (σ y)) = (k X0 X0) ∨ (σ y) ≠ (M.op (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq6877 eq7061
    | (have j0 := eq7061 X0
       grind)
    | exact resolve eq7061 eq6877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6877 eq7061
  have eq8618 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7038 eq182
    | (have j1 := eq7038 (σ x)
       grind)
    | exact resolve eq182 eq7038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7038
  have eq8673 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq7066 (σ x)
       grind)
    | (have r₁ := eq8618
       have r₂ := eq7066 (σ x)
       grind)
    | exact resolve eq8618 eq7066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7066 eq8618
  have eq8680 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq6862 eq8673
    | exact resolve eq8673 eq6862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6862 eq8673
  have eq8686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8680 eq7054
    | exact resolve eq7054 eq8680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7054 eq8680
  have eq8698 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq8686
  have eq8703 : y = (M.op y x) := by
    first
    | (have r₁ := eq8698
       have r₂ := eq27
       grind)
    | exact resolve eq8698 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8698
  have eq8715 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 x X0 y
       have i₂ := eq8703
       grind)
    | exact superpose eq8703 eq178
    | exact resolve eq178 eq8703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq8744 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq8715 X0 x
       have i₂ := eq8703
       grind)
    | exact superpose eq8703 eq8715
    | exact resolve eq8715 eq8703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8715
  have eq8857 : (k y y) = (M.op y x) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq8744 y
       grind)
    | exact superpose eq8744 eq182
    | exact resolve eq182 eq8744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8858 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq8744 y
       grind)
    | exact superpose eq8744 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8744 x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8744 y
       grind)
    | exact resolve eq13 eq8744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8869 : ∀ X0 : G, (k X0 y) = (M.op X0 x) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq6776 X0 y
       have i₂ := eq8744 X0
       grind)
    | exact superpose eq8744 eq6776
    | (have j0 := eq6776 X0 y
       grind)
    | exact resolve eq6776 eq8744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6776
  have eq8882 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8744 x
       grind)
    | exact superpose eq8744 eq18
    | (have j1 := eq8744 x
       grind)
    | exact resolve eq18 eq8744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq8744
  have eq8896 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq8882
       have i₂ := eq182 x
       grind)
    | exact superpose eq182 eq8882
    | exact resolve eq8882 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8882
  have eq8904 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq8858 X0
       have i₂ := eq8703
       grind)
    | exact superpose eq8703 eq8858
    | (have j0 := eq8858 X0
       grind)
    | exact resolve eq8858 eq8703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8858
  have eq8905 : y = (k y y) := by
    first
    | (have i₁ := eq8857
       have i₂ := eq8703
       grind)
    | exact superpose eq8703 eq8857
    | exact resolve eq8857 eq8703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8703 eq8857
  have eq8910 : ∀ X0 : G, (k X0 y) = (k X0 X0) ∨ y ≠ (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8904 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq8904
    | (have j0 := eq8904 X0
       grind)
    | exact resolve eq8904 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8904
  have eq8919 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq8896
       grind)
    | exact superpose eq8896 eq39
    | exact resolve eq39 eq8896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq8930 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8919
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8919
    | exact resolve eq8919 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8919
  have eq8937 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq8930
    | exact resolve eq8930 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8930
  have eq8942 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq8905
       grind)
    | exact superpose eq8905 eq40
    | exact resolve eq40 eq8905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8905
  have eq8956 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq8942
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8942
    | exact resolve eq8942 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8942
  have eq10329 : (k x x) = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq8869 x
       grind)
    | exact superpose eq8869 eq182
    | (have j1 := eq8869 x
       grind)
    | exact resolve eq182 eq8869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8869
  have eq10382 : (k x x) = (k x y) := by
    first
    | (have j1 := eq8910 x
       grind)
    | (have r₁ := eq10329
       have r₂ := eq8910 x
       grind)
    | exact resolve eq10329 eq8910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8910 eq10329
  have eq10389 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10382
       have i₂ := eq8896
       grind)
    | exact superpose eq8896 eq10382
    | exact resolve eq10382 eq8896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8896 eq10382
  have eq10397 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq10389
       grind)
    | exact superpose eq10389 eq40
    | exact resolve eq40 eq10389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq10389
  have eq10399 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq10397
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10397
    | exact resolve eq10397 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10397
  have eq10403 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10399
    | exact resolve eq10399 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10399
  have eq10407 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq10403 eq6839
    | exact resolve eq6839 eq10403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6839 eq10403
  have eq10415 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq10407
       have r₂ := eq27
       grind)
    | exact resolve eq10407 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10407
  have eq10483 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq10415 eq665
    | exact resolve eq665 eq10415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq10415
  have eq10490 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq8956 eq10483
    | exact resolve eq10483 eq8956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8956 eq10483
  have eq10546 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10490 eq26
    | (have j1 := eq10490 (σ x)
       grind)
    | exact resolve eq26 eq10490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10490
  have eq10553 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10546
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq10546
    | exact resolve eq10546 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq10546
  have eq10566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8937 eq10553
    | exact resolve eq10553 eq8937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8937 eq10553
  have eq10571 : False := by grind
  exact eq10571

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxx_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 (τ (σ X0)))) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 (σ X0) X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq18
    | exact resolve eq18 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq33
    | exact resolve eq33 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq30 (τ X0)
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq30
    | exact resolve eq30 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
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
  have eq43 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq40
    | exact resolve eq40 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq40
  have eq57 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq12 X0 (M.op (M.op X1 X0) X2)
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op x X1) X0)
       have r₂ := eq26 X0 X1 (M.op (M.op x X1) X0) x
       grind)
    | (have r₁ := eq12 (M.op (M.op x X1) X0) X1
       have r₂ := eq26 X0 X1 X1 x
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 (σ X0) X1 (σ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq26
    | exact resolve eq26 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (k X3 (M.op X0 X1)) ∨ (M.op X2 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X3) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X3 X1 X2 X0
       have i₂ := eq14 X3 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X3 (M.op X0 X1)
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op (τ X0) X1) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 X0 X2
       have i₂ := eq14 X2 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 X2 (M.op X0 X1)
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq4092 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) ∨ (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq4095 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) ∨ (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4092 X0 X1
       have j1 := eq67 X1 X0 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq4092 X1 X0
       have r₂ := eq67 X0 X1 X1 x
       grind)
    | (have r₁ := eq4092 (M.op X0 X1) X1
       have r₂ := eq67 X0 X1 x (M.op X1 (M.op X0 X1))
       grind)
    | exact resolve eq4092 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4092
  have eq16072 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4095 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq4095
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq4095 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095
  have eq16124 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq16072 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16072
  have eq16245 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq16124 X1 (σ X0)
       grind)
    | exact superpose eq16124 eq18
    | (have j1 := eq16124 X1 (σ X0)
       grind)
    | exact resolve eq18 eq16124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16246 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq16124 X1 (τ X0)
       grind)
    | exact superpose eq16124 eq21
    | (have j1 := eq16124 X1 (τ X0)
       grind)
    | exact resolve eq21 eq16124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16124
  have eq16465 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16245 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16245
    | (have j0 := eq16245 X1 (σ X0)
       grind)
    | exact resolve eq16245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16245
  have eq16540 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16465 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq16465
    | (have j0 := eq16465 X0 X1
       grind)
    | exact resolve eq16465 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16465
  have eq16688 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (σ X1))
       have i₂ := eq16246 X0 X1
       grind)
    | exact superpose eq16246 eq11
    | (have j1 := eq16246 X0 X1
       grind)
    | exact resolve eq11 eq16246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16246
  have eq17548 : ∀ X0 X1 : G, (τ (k X0 (σ (σ X1)))) = (σ (M.op (τ (τ X0)) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 (σ X1)
       have i₂ := eq16688 (τ X0) X1
       grind)
    | exact superpose eq16688 eq21
    | (have j1 := eq16688 (τ X0) X1
       grind)
    | exact resolve eq21 eq16688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16688
  have eq18148 : ∀ X0 X1 : G, (σ (τ (k X0 (σ X1)))) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16540 X1 (τ X0)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq16540
    | (have j0 := eq16540 X1 (τ X0)
       grind)
    | exact resolve eq16540 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16540
  have eq18196 : ∀ X0 X1 : G, (σ (τ (k X0 (σ X1)))) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18148 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18148
    | (have j0 := eq18148 X0 X1
       grind)
    | exact resolve eq18148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18148
  have eq18223 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18196 X0 X1
       have i₂ := eq11 (k X0 (σ X1))
       grind)
    | exact superpose eq11 eq18196
    | (have j0 := eq18196 X0 X1
       grind)
    | exact resolve eq18196 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18196
  have eq18240 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18223 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18223
    | (have j0 := eq18223 X0 X1
       grind)
    | exact resolve eq18223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18223
  have eq18559 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (τ X0)) ∨ (M.op (τ X0) (σ X1)) = (τ (k X0 (σ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 (σ X1)
       have i₂ := eq18240 (τ X0) X1
       grind)
    | exact superpose eq18240 eq21
    | (have j1 := eq18240 (τ X0) X1
       grind)
    | exact resolve eq21 eq18240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32268 : ∀ X0 X1 : G, (k X0 (σ (σ X1))) = (σ (σ (M.op (τ (τ X0)) X1))) ∨ (M.op X1 X1) = (M.op X1 (τ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 (σ (σ X1)))
       have i₂ := eq17548 X0 X1
       grind)
    | exact superpose eq17548 eq11
    | (have j1 := eq17548 X0 X1
       grind)
    | exact resolve eq11 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17548
  have eq35807 : ∀ X0 X1 X2 X3 : G, (M.op X1 (τ X2)) = (M.op X1 (M.op (σ (M.op X0 X0)) X3)) ∨ (M.op (τ X2) (σ X0)) = (τ (k X2 (σ (σ X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X3 (τ X2) X1 (σ X0)
       have i₂ := eq18559 X2 X0
       grind)
    | exact superpose eq18559 eq26
    | (have j1 := eq18559 X2 X0
       grind)
    | exact resolve eq26 eq18559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq18559
  have eq35854 : ∀ X0 X1 X2 : G, (M.op (τ X2) (σ X0)) = (τ (k X2 (σ (σ X0)))) ∨ (M.op X1 (σ X0)) = (M.op X1 (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35807 X0 X1 X2 x
       have i₂ := eq66 X0 X1 x
       grind)
    | exact superpose eq66 eq35807
    | (have j0 := eq35807 X0 X1 X2 x
       grind)
    | exact resolve eq35807 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq35807
  have eq36211 : ∀ X0 X1 X2 : G, (τ (σ (k X0 (τ (σ (σ X1)))))) = (M.op (τ (σ X0)) (σ X1)) ∨ (M.op X2 (σ X1)) = (M.op X2 (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35854 X1 X2 (σ X0)
       have i₂ := eq18 (σ (σ X1)) X0
       grind)
    | exact superpose eq18 eq35854
    | (have j0 := eq35854 X1 X2 (σ X0)
       grind)
    | exact resolve eq35854 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35854
  have eq36288 : ∀ X0 X1 X2 : G, (M.op X0 (σ X1)) = (τ (σ (k X0 (τ (σ (σ X1)))))) ∨ (M.op X2 (σ X1)) = (M.op X2 (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36211 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36211
    | (have j0 := eq36211 X0 X1 X2
       grind)
    | exact resolve eq36211 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36211
  have eq36314 : ∀ X0 X1 X2 : G, (M.op X0 (σ X1)) = (k X0 (τ (σ (σ X1)))) ∨ (M.op X2 (σ X1)) = (M.op X2 (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36288 X0 X1 X2
       have i₂ := eq10 (k X0 (τ (σ (σ X1))))
       grind)
    | exact superpose eq10 eq36288
    | (have j0 := eq36288 X0 X1 X2
       grind)
    | exact resolve eq36288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36288
  have eq36332 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X2 (σ X1)) = (M.op X2 (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36314 X0 X1 X2
       have i₂ := eq10 (σ X1)
       grind)
    | exact superpose eq10 eq36314
    | (have j0 := eq36314 X0 X1 X2
       grind)
    | exact resolve eq36314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36314
  have eq36334 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X2 X0) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36332 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36332
    | (have j0 := eq36332 X0 X1 X2
       grind)
    | exact resolve eq36332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36332
  have eq36525 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36334 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36334
    | exact resolve eq36334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36609 : ∀ X0 X1 X2 : G, (σ (k X0 (τ (σ X1)))) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (σ X1) X0
       have i₂ := eq36334 (σ X0) X1 X2
       grind)
    | exact superpose eq36334 eq18
    | (have j1 := eq36334 (σ X0) X1 X2
       grind)
    | exact resolve eq18 eq36334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36334
  have eq36616 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36609 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq36609
    | (have j0 := eq36609 X0 X1 X2
       grind)
    | exact resolve eq36609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36609
  have eq47709 : ∀ X0 X1 : G, (σ (k X0 (τ (σ (σ X1))))) = (σ (σ (M.op (τ (τ (σ X0))) X1))) ∨ (M.op X1 X1) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ (σ X1)) X0
       have i₂ := eq32268 (σ X0) X1
       grind)
    | exact superpose eq32268 eq18
    | (have j1 := eq32268 (σ X0) X1
       grind)
    | exact resolve eq18 eq32268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32268
  have eq47724 : ∀ X0 X1 : G, (σ (σ (M.op (τ X0) X1))) = (σ (k X0 (τ (σ (σ X1))))) ∨ (M.op X1 X1) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq47709 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47709
    | (have j0 := eq47709 X0 X1
       grind)
    | exact resolve eq47709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47709
  have eq47810 : ∀ X0 X1 : G, (σ (k X0 (σ X1))) = (σ (σ (M.op (τ X0) X1))) ∨ (M.op X1 X1) = (M.op X1 (τ (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq47724 X0 X1
       have i₂ := eq10 (σ X1)
       grind)
    | exact superpose eq10 eq47724
    | (have j0 := eq47724 X0 X1
       grind)
    | exact resolve eq47724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47724
  have eq47870 : ∀ X0 X1 : G, (σ (k X0 (σ X1))) = (σ (σ (M.op (τ X0) X1))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47810 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47810
    | (have j0 := eq47810 X0 X1
       grind)
    | exact resolve eq47810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47810
  have eq48116 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (σ (M.op (τ X1) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47870 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47870
    | (have j0 := eq47870 X1 (τ X0)
       grind)
    | exact resolve eq47870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47870
  have eq48311 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (σ (k X1 X0)) = (σ (σ (M.op (τ X1) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48116 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq48116
    | (have j0 := eq48116 X0 X1
       grind)
    | exact resolve eq48116 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48116
  have eq51782 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ X1) (τ X1)) = (k (τ X1) (τ X0)) ∨ (σ (k X1 X0)) = (σ (σ (M.op (τ X1) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (τ X1)
       have i₂ := eq48311 X0 X1
       grind)
    | exact superpose eq48311 eq81
    | (have j0 := eq81 X0 (τ X1)
       have j1 := eq48311 X0 X1
       grind)
    | (have r₁ := eq81 X0 (τ X1)
       have r₂ := eq48311 X0 X1
       grind)
    | exact resolve eq81 eq48311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq48311
  have eq51897 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (k (τ X1) (τ X0)) ∨ (σ (k X1 X0)) = (σ (σ (M.op (τ X1) (τ X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq51782 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51782
  have eq51960 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (τ (k X1 (σ (τ X0)))) ∨ (σ (k X1 X0)) = (σ (σ (M.op (τ X1) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51897 X0 X1
       have i₂ := eq21 X1 (τ X0)
       grind)
    | exact superpose eq21 eq51897
    | (have j0 := eq51897 X0 X1
       grind)
    | exact resolve eq51897 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq51897
  have eq52044 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (τ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (σ (M.op (τ X1) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51960 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51960
    | (have j0 := eq51960 X0 X1
       grind)
    | exact resolve eq51960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51960
  have eq52089 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (τ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (σ (M.op (τ X1) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52044 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq52044
    | (have j0 := eq52044 X0 X1
       grind)
    | exact resolve eq52044 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq52044
  have eq52987 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (σ (M.op (τ X0) (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq52089 X1 X0
       grind)
    | exact superpose eq52089 eq11
    | (have j1 := eq52089 X1 X0
       grind)
    | exact resolve eq11 eq52089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52089
  have eq53054 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (σ (M.op (τ X0) (τ X1)))) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52987 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq52987
    | (have j0 := eq52987 X0 X1
       grind)
    | exact resolve eq52987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52987
  have eq53412 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (σ (M.op (τ X0) (τ X1))))) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq53054 X0 X1
       grind)
    | exact superpose eq53054 eq10
    | (have j1 := eq53054 X0 X1
       grind)
    | exact resolve eq10 eq53054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53054
  have eq53484 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53412 X0 X1
       have i₂ := eq10 (σ (M.op (τ X0) (τ X1)))
       grind)
    | exact superpose eq10 eq53412
    | (have j0 := eq53412 X0 X1
       grind)
    | exact resolve eq53412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53412
  have eq53898 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ (σ X1)))) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18240 X0 X1
       have i₂ := eq53484 X0 (σ X1)
       grind)
    | exact superpose eq53484 eq18240
    | (have j0 := eq18240 X0 X1
       have j1 := eq53484 X0 (σ X1)
       grind)
    | exact resolve eq18240 eq53484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18240 eq53484
  have eq54013 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ (σ X1)))) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq53898 X0 X1
       have j1 := eq57 X1 X0
       grind)
    | (have r₁ := eq53898 X1 X0
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq53898 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq53898
  have eq54079 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54013 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq54013
    | (have j0 := eq54013 X0 X1
       grind)
    | exact resolve eq54013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54013
  have eq56349 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54079 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54079
    | (have j0 := eq54079 (σ X0) X1
       grind)
    | exact resolve eq54079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54079
  have eq56579 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56349 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq56349
    | (have j0 := eq56349 X0 X1
       grind)
    | exact resolve eq56349 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56349
  have eq56607 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56579 X0 X1
       have i₂ := eq18 (σ X1) X0
       grind)
    | exact superpose eq18 eq56579
    | (have j0 := eq56579 X0 X1
       grind)
    | exact resolve eq56579 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq56579
  have eq56628 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56607 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq56607
    | (have j0 := eq56607 X0 X1
       grind)
    | exact resolve eq56607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56607
  have eq63441 : (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have j0 := eq56628 x y
       grind)
    | (have r₁ := eq56628 x y
       have r₂ := eq16
       grind)
    | exact resolve eq56628 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56628
  have eq64143 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq36616 x y X0
       have i₂ := eq63441
       grind)
    | exact superpose eq63441 eq36616
    | (have j0 := eq36616 y x X0
       grind)
    | exact resolve eq36616 eq63441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36616
  have eq64150 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq63441
       grind)
    | exact superpose eq63441 eq10
    | exact resolve eq10 eq63441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63441
  have eq64230 : (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq64150
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq64150
    | exact resolve eq64150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64150
  have eq64687 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq36525 y x X0
       have i₂ := eq64230
       grind)
    | exact superpose eq64230 eq36525
    | (have j0 := eq36525 x y x
       grind)
    | exact resolve eq36525 eq64230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36525 eq64230
  have eq65149 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq64687 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64687
  have eq65150 : (M.op x y) = (M.op x x) := by grind
  clear eq65149
  have eq65156 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65150
       grind)
    | exact superpose eq65150 eq16
    | exact resolve eq16 eq65150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65150
  have eq65162 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq64143 X0
       grind)
    | (have r₁ := eq64143 X0
       have r₂ := eq65156
       grind)
    | exact resolve eq64143 eq65156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64143
  have eq65163 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq65156
       have i₂ := eq65162 (σ x)
       grind)
    | exact superpose eq65162 eq65156
    | exact resolve eq65156 eq65162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65156 eq65162
  have eq65164 : False := by grind
  exact eq65164

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq74 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op (M.op X2 X1) X3) X0) = (k (M.op (M.op X2 X1) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) X3) X0
       have i₂ := eq63 X3 X1 X0 X2
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq63 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq63 X0 X1 X1 X3
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq15
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq76 (τ X0)
       grind)
    | exact superpose eq76 eq31
    | exact resolve eq31 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq82
    | exact resolve eq82 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq80
    | exact resolve eq80 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq80
  have eq108 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) ≠ (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1128 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq108 X1 X0
       grind)
    | exact superpose eq108 eq22
    | (have j1 := eq108 X1 X0
       grind)
    | exact resolve eq22 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1129 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq108 X1 (σ X0)
       grind)
    | exact superpose eq108 eq15
    | (have j1 := eq108 X1 (σ X0)
       grind)
    | exact resolve eq15 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1159 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) ≠ (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq118 X1 X0
       grind)
    | exact superpose eq118 eq18
    | (have j1 := eq118 X1 X0
       grind)
    | exact resolve eq18 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1185 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op (τ X1) X0) = (M.op (τ X1) (τ X1)) := by
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
  clear eq18
  have eq1188 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq1205 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1188 X0 X1
       have i₂ := eq91 X1
       grind)
    | exact superpose eq91 eq1188
    | (have j0 := eq1188 X0 X1
       grind)
    | exact resolve eq1188 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1206 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ X1) X0) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1185 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq1185
    | (have j0 := eq1185 X0 X1
       grind)
    | exact resolve eq1185 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1219 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1205 X0 X1
       have j1 := eq1129 X0 X1
       grind)
    | (have r₁ := eq1205 X0 X1
       have r₂ := eq1129 X0 X1
       grind)
    | exact resolve eq1205 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq1205
  have eq1220 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1206 X0 X1
       have j1 := eq1159 X0 X1
       grind)
    | (have r₁ := eq1206 X0 X1
       have r₂ := eq1159 X0 X1
       grind)
    | exact resolve eq1206 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159 eq1206
  have eq1230 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1220 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1220
    | exact resolve eq1220 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1244 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 (τ X1))
       have i₂ := eq1220 X0 X1
       grind)
    | exact superpose eq1220 eq10
    | (have j1 := eq1220 X0 X1
       grind)
    | exact resolve eq10 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1267 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1244 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq1244
    | (have j0 := eq1244 X0 X1
       grind)
    | exact resolve eq1244 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1275 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1230 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1230
    | (have j0 := eq1230 X0 X1
       grind)
    | exact resolve eq1230 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1284 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1275 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1275
    | (have j0 := eq1275 (τ X1) (τ X0)
       grind)
    | exact resolve eq1275 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1289 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1275 X1 (τ X0)
       grind)
    | exact superpose eq1275 eq17
    | (have j1 := eq1275 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1291 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq1275 X1 X0
       grind)
    | exact superpose eq1275 eq10
    | (have j1 := eq1275 X1 X0
       grind)
    | exact resolve eq10 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1327 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1291 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq1291
    | (have j0 := eq1291 X0 X1
       grind)
    | exact resolve eq1291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1328 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1284 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1284
    | (have j0 := eq1284 X0 X1
       grind)
    | exact resolve eq1284 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1348 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq1327 (σ X0) X1
       grind)
    | exact superpose eq1327 eq28
    | (have j1 := eq1327 (σ X0) X1
       grind)
    | exact resolve eq28 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1482 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1348 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1348
    | exact resolve eq1348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1526 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1482 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1482
    | (have j0 := eq1482 X0 X1
       grind)
    | exact resolve eq1482 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq1535 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1526 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1526
    | (have j0 := eq1526 (τ X0) (τ X1)
       grind)
    | exact resolve eq1526 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1624 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1219 x y
       grind)
    | exact superpose eq1219 eq16
    | (have j1 := eq1219 x y
       grind)
    | exact resolve eq16 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq1219 X0 X1
       grind)
    | exact superpose eq1219 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq1219 X0 X1
       grind)
    | exact resolve eq12 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1655 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1648 X0 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq1648
    | (have j0 := eq1648 X0 X1
       grind)
    | exact resolve eq1648 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1675 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1655 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1655
    | (have j0 := eq1655 X0 X1
       grind)
    | exact resolve eq1655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq2153 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) X1) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1220 (τ X0) X1
       have i₂ := eq1328 X1 X0
       grind)
    | exact superpose eq1328 eq1220
    | (have j0 := eq1220 (τ X0) X1
       have j1 := eq1328 X0 X1
       grind)
    | exact resolve eq1220 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq1328
  have eq2187 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2153 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2153
    | (have j0 := eq2153 X0 X1
       grind)
    | exact resolve eq2153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq3042 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1128 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1128
    | exact resolve eq1128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq3095 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3042 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq3042
    | (have j0 := eq3042 X0 X1
       grind)
    | exact resolve eq3042 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq3102 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (σ (τ (M.op X0 X0))) ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3095 X0 X1
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq3095
    | (have j0 := eq3095 X0 X1
       grind)
    | exact resolve eq3095 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq3107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3102 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3102
    | (have j0 := eq3102 X0 X1
       grind)
    | (have r₁ := eq3102 X1 X1
       have r₂ := eq11 (M.op X1 X1)
       grind)
    | exact resolve eq3102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102
  have eq3139 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op (τ X0) X1) ∨ (τ (k X1 (τ X0))) = (τ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3107 (τ X0) X1
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq3107
    | (have j0 := eq3107 (τ X0) X1
       grind)
    | exact resolve eq3107 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107
  have eq15029 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (k (τ X1) (τ X0))) = (τ (M.op (τ X1) (τ X0))) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3139 X0 (τ X1)
       have i₂ := eq1535 X1 X0
       grind)
    | exact superpose eq1535 eq3139
    | (have j0 := eq3139 X0 (τ X1)
       have j1 := eq1535 X1 X0
       grind)
    | exact resolve eq3139 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3139
  have eq15075 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq1535 X0 X1
       grind)
    | exact superpose eq1535 eq13
    | (have j0 := eq13 (τ X1) (τ X0)
       have j1 := eq1535 X0 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq1535 X0 X1
       grind)
    | exact resolve eq13 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq15086 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq15075 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15075
  have eq15097 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15086 X0 X1
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq15086
    | (have j0 := eq15086 X0 X1
       grind)
    | exact resolve eq15086 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15086
  have eq15136 : ∀ X0 X1 : G, (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) ∨ (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15029 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq15029
    | (have j0 := eq15029 X0 X1
       grind)
    | exact resolve eq15029 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15029
  have eq15137 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq15136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15136
  have eq15156 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15097 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq15097
    | (have j0 := eq15097 X0 X1
       grind)
    | exact resolve eq15097 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15097
  have eq15190 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq15156 X0 X1
       have j1 := eq15137 X0 X1
       grind)
    | (have r₁ := eq15156 X0 X1
       have r₂ := eq15137 X0 X1
       grind)
    | exact resolve eq15156 eq15137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15137 eq15156
  have eq15202 : ∀ X0 X1 : G, (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X1 X0))) ∨ (τ (k X1 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15190 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq15190
    | (have j0 := eq15190 X0 X1
       grind)
    | exact resolve eq15190 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15190
  have eq20357 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = (k (M.op (M.op X0 X1) X2) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq74 X1 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq20477 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (k (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20357 (σ X0) (σ X0) x
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq20357
    | exact resolve eq20357 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20771 : ∀ X0 X1 : G, (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0))) = (k (τ (M.op (σ (M.op X0 X0)) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ (M.op X0 X0)) X1) X0
       have i₂ := eq20477 X0 X1
       grind)
    | exact superpose eq20477 eq22
    | exact resolve eq22 eq20477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20477
  have eq39087 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (σ (τ (τ (k X0 X1)))) ∨ (τ (k X0 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (τ X0) (τ X1))
       have i₂ := eq15202 X1 X0
       grind)
    | exact superpose eq15202 eq11
    | (have j1 := eq15202 X1 X0
       grind)
    | exact resolve eq11 eq15202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15202
  have eq39243 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39087 X0 X1
       have i₂ := eq11 (τ (k X0 X1))
       grind)
    | exact superpose eq11 eq39087
    | (have j0 := eq39087 X0 X1
       grind)
    | exact resolve eq39087 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39087
  have eq39315 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ (k (σ X0) X1)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39243 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39243
    | (have j0 := eq39243 (σ X0) X1
       grind)
    | exact resolve eq39243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39243
  have eq39593 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (k (σ X0) X1)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq39315 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq39315
    | (have j0 := eq39315 X0 X1
       grind)
    | exact resolve eq39315 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39315
  have eq39646 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (τ (σ (M.op X0 X0))) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39593 X0 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq39593
    | (have j0 := eq39593 X0 X1
       grind)
    | exact resolve eq39593 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39593
  have eq39677 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) X1)) ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39646 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq39646
    | (have j0 := eq39646 X0 X1
       grind)
    | exact resolve eq39646 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39646
  have eq39695 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39677 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq39677
    | (have j0 := eq39677 X0 X1
       grind)
    | exact resolve eq39677 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39677
  have eq39716 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39695 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq39695
    | exact resolve eq39695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39695
  have eq39945 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39716 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39716
    | exact resolve eq39716 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40106 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq1624
       have i₂ := eq39716 y x
       grind)
    | exact superpose eq39716 eq1624
    | (have j1 := eq39716 y x
       grind)
    | exact resolve eq1624 eq39716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39716 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39716
  have eq40108 : (k x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq40106
  have eq40189 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39945 X0 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq39945
    | (have j0 := eq39945 X0 X1
       grind)
    | exact resolve eq39945 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39945
  have eq40207 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40107 X0 (M.op (M.op X2 X1) X3)
       have i₂ := eq63 X3 X1 X0 X2
       grind)
    | exact superpose eq63 eq40107
    | (have j0 := eq40107 X0 X1
       grind)
    | (have r₁ := eq40107 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq63 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq40107 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq63 X0 X1 X1 X3
       grind)
    | exact resolve eq40107 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40107
  have eq42142 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40207 X0 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40207
  have eq42507 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op (M.op X1 (σ X0)) X2)
       have i₂ := eq42142 (σ X0) X1 X2
       grind)
    | exact superpose eq42142 eq28
    | exact resolve eq28 eq42142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42142
  have eq42571 : ∀ X0 X1 X2 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (M.op (M.op X1 (σ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42507 X0 X1 X2
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq42507
    | exact resolve eq42507 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42507
  have eq42676 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (τ (M.op (M.op X1 (σ X0)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42571 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq42571
    | exact resolve eq42571 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42571
  have eq43279 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (k (τ (M.op (σ (M.op X0 X0)) (σ X1))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42676 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq20771 X0 (σ X1)
       grind)
    | exact superpose eq20771 eq42676
    | exact resolve eq42676 eq20771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20771 eq42676
  have eq50469 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (k (τ (M.op (σ (σ (M.op X0 X0))) (σ X1))) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq43279 (σ X0) X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq43279
    | exact resolve eq43279 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50547 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (k (τ (M.op (σ (M.op X1 X1)) X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43279 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43279
    | exact resolve eq43279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43279
  have eq50865 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (k (τ (M.op (σ (M.op X1 X1)) X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50547 X0 X1
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq50547
    | exact resolve eq50547 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq50547
  have eq55215 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (k (τ X1) (k (τ (M.op (σ (σ (M.op X0 X0))) X1)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq50865 X1 (σ X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq50865
    | exact resolve eq50865 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50865
  have eq64902 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (k (τ (M.op (σ (σ (σ (M.op X0 X0)))) (σ X1))) (σ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50469 (σ X0) X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq50469
    | exact resolve eq50469 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50469
  have eq70759 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40189 x y
       grind)
    | exact superpose eq40189 eq16
    | (have j1 := eq40189 x y
       grind)
    | exact resolve eq16 eq40189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40189
  have eq74330 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1675 x y
       have i₂ := eq40108
       grind)
    | exact superpose eq40108 eq1675
    | (have j0 := eq1675 x y
       grind)
    | exact resolve eq1675 eq40108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675 eq40108
  have eq74444 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq74330
  have eq74445 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
  clear eq74444
  have eq75180 : (σ y) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
  clear eq74445
  have eq76750 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (k (τ X1) (k (τ (M.op (σ (σ (σ (M.op X0 X0)))) X1)) (σ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq55215 (σ X0) X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq55215
    | exact resolve eq55215 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55215
  have eq648829 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2187 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2187
    | (have j0 := eq2187 X1 (σ X0)
       grind)
    | exact resolve eq2187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187
  have eq650022 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 (τ X1))
       have i₂ := eq648829 X0 X1
       grind)
    | exact superpose eq648829 eq10
    | (have j1 := eq648829 X0 X1
       grind)
    | exact resolve eq10 eq648829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648829
  have eq650303 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq650022 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq650022
    | (have j0 := eq650022 X0 X1
       grind)
    | exact resolve eq650022 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650022
  have eq651325 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op X1 (τ (σ X0))) = X1 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq650303 X1 (σ X0)
       grind)
    | exact superpose eq650303 eq28
    | (have j1 := eq650303 X1 (σ X0)
       grind)
    | exact resolve eq28 eq650303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq650303
  have eq651774 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X1 (τ (σ X0))) = X1 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq651325 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq651325
    | (have j0 := eq651325 X0 X1
       grind)
    | exact resolve eq651325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651325
  have eq651986 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 (τ (σ X0))) = X1 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq651774 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq651774
    | (have j0 := eq651774 X0 X1
       grind)
    | exact resolve eq651774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651774
  have eq652127 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq651986 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq651986
    | (have j0 := eq651986 X0 X1
       grind)
    | exact resolve eq651986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651986
  have eq652230 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq652127 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq652127
    | (have j0 := eq652127 X0 X1
       grind)
    | exact resolve eq652127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652127
  have eq652912 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X1) = (k (M.op X0 X2) X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20357 X1 X0 X2
       have i₂ := eq652230 X0 X1
       grind)
    | exact superpose eq652230 eq20357
    | (have j1 := eq652230 X1 X0
       grind)
    | exact resolve eq20357 eq652230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20357 eq652230
  have eq876412 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ (M.op X0 X2) = (k X0 X2) ∨ (k X2 X0) = X2 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq652912 X1 X1 (τ X0)
       have i₂ := eq1289 X0 X1
       grind)
    | exact superpose eq1289 eq652912
    | (have j0 := eq652912 X0 X2 X2
       have j1 := eq1289 X1 X0
       grind)
    | exact resolve eq652912 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289 eq652912
  have eq877212 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X2 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq876412 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876412
  have eq884978 : ∀ X0 X1 X2 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k X2 X1) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq877212 X1 X0 X2
       grind)
    | exact superpose eq877212 eq10
    | (have j1 := eq877212 X1 X1 X2
       grind)
    | exact resolve eq10 eq877212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877212
  have eq885295 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X2 X1) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq884978 X0 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq884978
    | (have j0 := eq884978 X0 X1 X2
       grind)
    | exact resolve eq884978 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq884978
  have eq886796 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) X1) ∨ (τ X0) = (k (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq885295 X0 X1 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885295
  have eq886799 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq886796 X0 X1
       have j1 := eq1267 X1 X0
       grind)
    | (have r₁ := eq886796 X1 X0
       have r₂ := eq1267 X0 X1
       grind)
    | exact resolve eq886796 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq886796
  have eq888107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq886799 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq886799
    | exact resolve eq886799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886799
  have eq890675 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1624
       have i₂ := eq888107 y x
       grind)
    | exact superpose eq888107 eq1624
    | (have j1 := eq888107 y x
       grind)
    | exact resolve eq1624 eq888107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624 eq888107
  have eq890755 : y = (k y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq890675
  have eq891061 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq75180
       have i₂ := eq890755
       grind)
    | exact superpose eq890755 eq75180
    | exact resolve eq75180 eq890755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75180 eq890755
  have eq891319 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq891061
  have eq891320 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq891319
  have eq891427 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ x) X0 (σ y)
       have i₂ := eq891320
       grind)
    | exact superpose eq891320 eq63
    | exact resolve eq63 eq891320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq895063 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq891427 X0 (σ x)
       have i₂ := eq891320
       grind)
    | exact superpose eq891320 eq891427
    | exact resolve eq891427 eq891320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891427
  have eq897229 : ∀ X0 : G, (M.op y y) = (k y (k (τ (M.op (σ (σ (σ (M.op X0 X0)))) (σ x))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq64902 X0 y
       have i₂ := eq895063 (σ (σ (σ (M.op X0 X0))))
       grind)
    | exact superpose eq895063 eq64902
    | exact resolve eq64902 eq895063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64902
  have eq897236 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq895063 (σ x)
       grind)
    | exact superpose eq895063 eq16
    | exact resolve eq16 eq895063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897291 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) (k (τ (M.op (σ (σ (σ (M.op X0 X0)))) (σ x))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq76750 X0 (σ y)
       have i₂ := eq895063 (σ (σ (σ (M.op X0 X0))))
       grind)
    | exact superpose eq895063 eq76750
    | exact resolve eq76750 eq895063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76750
  have eq897525 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) = (k y (k (τ (M.op (σ (σ (σ (M.op X0 X0)))) (σ x))) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq897291 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq897291
    | exact resolve eq897291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897291
  have eq897541 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq897236
       have i₂ := eq91 x
       grind)
    | exact superpose eq91 eq897236
    | exact resolve eq897236 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq897236
  have eq897968 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq897525 x
       have i₂ := eq897229 x
       grind)
    | exact superpose eq897229 eq897525
    | exact resolve eq897525 eq897229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897229 eq897525
  have eq898202 : (M.op y y) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq897968
       have i₂ := eq895063 (σ y)
       grind)
    | exact superpose eq895063 eq897968
    | exact resolve eq897968 eq895063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895063 eq897968
  have eq898347 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq898202
       have i₂ := eq891320
       grind)
    | exact superpose eq891320 eq898202
    | exact resolve eq898202 eq891320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891320 eq898202
  have eq898438 : y = (M.op y y) := by
    first
    | (have i₁ := eq898347
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq898347
    | exact resolve eq898347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898347
  have eq898653 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq898438
       grind)
    | exact superpose eq898438 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq898438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898438
  have eq899072 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq898653 X0
       have j1 := eq1327 X0 y
       grind)
    | (have r₁ := eq898653 X0
       have r₂ := eq1327 X0 y
       grind)
    | exact resolve eq898653 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327 eq898653
  have eq901303 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70759
       have i₂ := eq899072 x
       grind)
    | exact superpose eq899072 eq70759
    | exact resolve eq70759 eq899072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70759 eq899072
  have eq901319 : (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq901303
  have eq901322 : False := by grind
  exact eq901322

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq74 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op (M.op X2 X1) X3) X0) = (k (M.op (M.op X2 X1) X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) X3) X0
       have i₂ := eq63 X3 X1 X0 X2
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq63 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq63 X0 X1 X1 X3
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 (M.op (M.op X0 X1) X2)) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op (M.op X0 X1) X2)
       have i₂ := eq63 X2 X1 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X3 (M.op (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X3 X1) X0)
       have r₂ := eq63 X0 X1 (M.op (M.op X3 X1) X0) X3
       grind)
    | (have r₁ := eq12 (M.op (M.op X3 X1) X0) X1
       have r₂ := eq63 X0 X1 X1 X3
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X1) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op X3 X1) = (k X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 X0 X1 X2 X3
       have i₂ := eq63 X2 X1 X3 X0
       grind)
    | exact superpose eq63 eq75
    | (have j0 := eq75 X0 X1 X2 X3
       grind)
    | (have r₁ := eq75 X0 X1 X2 (M.op (M.op X3 X1) X0)
       have r₂ := eq63 X0 X1 (M.op (M.op X0 X1) X2) X3
       grind)
    | (have r₁ := eq75 X0 (M.op (M.op X3 X1) X0) X2 X1
       have r₂ := eq63 X0 X1 (M.op (M.op X0 (M.op (M.op X3 X1) X0)) X2) X3
       grind)
    | exact resolve eq75 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq15
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq76 (τ X0)
       grind)
    | exact superpose eq76 eq31
    | exact resolve eq31 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq82
    | exact resolve eq82 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq80
    | exact resolve eq80 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq80
  have eq106 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (σ X0) X1 (σ X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq63
    | exact resolve eq63 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (τ X0) X1 (τ X0)
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq63
    | exact resolve eq63 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) ≠ (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 X1 (σ (M.op X0 X0))
       have i₂ := eq91 (M.op X0 X0)
       grind)
    | exact superpose eq91 eq106
    | exact resolve eq106 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq108 X1 (σ X0)
       grind)
    | exact superpose eq108 eq28
    | (have j1 := eq108 X1 (σ X0)
       grind)
    | exact resolve eq28 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1125 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1117 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1117
    | (have j0 := eq1117 X0 X1
       grind)
    | exact resolve eq1117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1142 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) ≠ (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq118 X1 X0
       grind)
    | exact superpose eq118 eq18
    | (have j1 := eq118 X1 X0
       grind)
    | exact resolve eq18 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1168 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (M.op (τ X1) X0) = (M.op (τ X1) (τ X1)) := by
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
  have eq1189 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ X1) X0) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1168 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq1168
    | (have j0 := eq1168 X0 X1
       grind)
    | exact resolve eq1168 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1203 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1189 X0 X1
       have j1 := eq1142 X0 X1
       grind)
    | (have r₁ := eq1189 X0 X1
       have r₂ := eq1142 X0 X1
       grind)
    | exact resolve eq1189 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq1189
  have eq1213 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1203
    | exact resolve eq1203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1258 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1213 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1213
    | (have j0 := eq1213 X0 X1
       grind)
    | exact resolve eq1213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1272 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1258 X1 (τ X0)
       grind)
    | exact superpose eq1258 eq17
    | (have j1 := eq1258 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq1386 : ∀ X0 X1 X2 X3 : G, (k X2 (σ X0)) = (σ (M.op (τ X2) X0)) ∨ (M.op X1 (τ X2)) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X3 (τ X2) X1 X0
       have i₂ := eq1272 X2 X0
       grind)
    | exact superpose eq1272 eq63
    | (have j1 := eq1272 X2 X0
       grind)
    | exact resolve eq63 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : ∀ X0 X1 X2 X3 : G, (k X3 (σ (M.op X0 X1))) = (σ (M.op (τ X3) (M.op X0 X1))) ∨ (M.op X2 X1) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 (τ X3) X1 X2 X0
       have i₂ := eq1272 X3 (M.op X0 X1)
       grind)
    | exact superpose eq1272 eq63
    | (have j1 := eq1272 X3 (M.op X0 X1)
       grind)
    | exact resolve eq63 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9989 : ∀ X0 X1 X2 X3 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X0) = (M.op X2 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1386 X0 X1 (σ X0) X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1386
    | exact resolve eq1386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq10130 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X0) = (M.op X2 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9989 X0 X1 X2 X3
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9989
    | (have j0 := eq9989 X0 X1 X2 X3
       grind)
    | exact resolve eq9989 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9989
  have eq10208 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X2 X0) = (M.op X2 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq10130 X0 X1 X2 X3
       grind)
    | exact superpose eq10130 eq10
    | (have j1 := eq10130 X0 X1 X2 X3
       grind)
    | exact resolve eq10 eq10130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10130
  have eq10269 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X0) = (M.op X2 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10208 X0 X1 X2 X3
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq10208
    | (have j0 := eq10208 X0 X1 X2 X3
       grind)
    | exact resolve eq10208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10208
  have eq10344 : ∀ X0 X1 X2 X3 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X2 (σ X0)) = (M.op X2 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq10269 (σ X0) X1 X2 X3
       grind)
    | exact superpose eq10269 eq28
    | (have j1 := eq10269 (σ X0) X1 X2 X3
       grind)
    | exact resolve eq28 eq10269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10269
  have eq18572 : ∀ X0 X1 X2 X3 X4 X5 : G, (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (M.op X2 X1) X3))) ∨ (M.op X4 (σ X0)) = (M.op X4 (M.op (M.op (M.op X2 X1) X3) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq10344 X0 (M.op (M.op X2 X1) X3) X4 X5
       have i₂ := eq63 X3 X1 (σ X0) X2
       grind)
    | exact superpose eq63 eq10344
    | (have j0 := eq10344 X0 (M.op (M.op X2 X1) X3) X4 X5
       grind)
    | exact resolve eq10344 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10344
  have eq18766 : ∀ X0 X1 X2 X3 X4 : G, (τ (M.op (σ X0) X1)) = (k X0 (τ (M.op (M.op X2 X1) X3))) ∨ (M.op X4 X3) = (M.op X4 (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18572 X0 X1 X2 X3 X4 x
       have i₂ := eq63 x X3 X4 (M.op X2 X1)
       grind)
    | exact superpose eq63 eq18572
    | (have j0 := eq18572 X0 X1 X2 X3 X4 x
       grind)
    | exact resolve eq18572 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18572
  have eq20310 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = (k (M.op (M.op X0 X1) X2) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq74 X1 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq20430 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (k (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20310 (σ X0) (σ X0) x
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq20310
    | exact resolve eq20310 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20446 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) = (k (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20310 (τ X0) (τ X0) x
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq20310
    | exact resolve eq20310 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20522 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op X0 (σ X1)) X2)) X1) = (τ (M.op (M.op (M.op X0 (σ X1)) X2) (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op X0 (σ X1)) X2) X1
       have i₂ := eq20310 X0 (σ X1) X2
       grind)
    | exact superpose eq20310 eq22
    | exact resolve eq22 eq20310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20724 : ∀ X0 X1 : G, (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0))) = (k (τ (M.op (σ (M.op X0 X0)) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ (M.op X0 X0)) X1) X0
       have i₂ := eq20430 X0 X1
       grind)
    | exact superpose eq20430 eq22
    | exact resolve eq22 eq20430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20430
  have eq21330 : ∀ X0 X1 : G, (σ (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0))) = (k (σ (M.op (τ (M.op X0 X0)) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ (M.op X0 X0)) X1)
       have i₂ := eq20446 X0 X1
       grind)
    | exact superpose eq20446 eq18
    | exact resolve eq18 eq20446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20446
  have eq52027 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq77 X1 X0 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq52390 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X1))) = (σ (M.op (τ X2) (M.op X0 X1))) ∨ (M.op X1 X1) = (k X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52027 X1 X0 (τ X2)
       have i₂ := eq1272 X2 (M.op X0 X1)
       grind)
    | exact superpose eq1272 eq52027
    | (have j1 := eq1272 X2 (M.op X0 X1)
       grind)
    | exact resolve eq52027 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272 eq52027
  have eq636689 : ∀ X0 X1 X2 X3 : G, (τ (k X0 (σ (M.op X1 X2)))) = (M.op (τ X0) (M.op X1 X2)) ∨ (M.op X3 X2) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (M.op (τ X0) (M.op X1 X2))
       have i₂ := eq1388 X1 X2 X3 X0
       grind)
    | exact superpose eq1388 eq10
    | (have j1 := eq1388 X1 X2 X3 X3
       grind)
    | exact resolve eq10 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq636960 : ∀ X0 X1 X2 X3 : G, (k (τ X0) (M.op X1 X2)) = (M.op (τ X0) (M.op X1 X2)) ∨ (M.op X3 X2) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq636689 X0 X1 X2 X3
       have i₂ := eq22 X0 (M.op X1 X2)
       grind)
    | exact superpose eq22 eq636689
    | (have j0 := eq636689 X0 X1 X2 X3
       grind)
    | exact resolve eq636689 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636689
  have eq647852 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X2)) ∨ (M.op X3 X2) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq636960 (σ X0) X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq636960
    | (have j0 := eq636960 X0 X1 X2 X3
       grind)
    | exact resolve eq636960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636960
  have eq690485 : ∀ X0 X1 X2 : G, (τ (k X0 (σ (M.op X1 X2)))) = (M.op (τ X0) (M.op X1 X2)) ∨ (M.op X2 X2) = (k X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op (τ X0) (M.op X1 X2))
       have i₂ := eq52390 X1 X2 X0
       grind)
    | exact superpose eq52390 eq10
    | (have j1 := eq52390 X1 X2 X2
       grind)
    | exact resolve eq10 eq52390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52390
  have eq690763 : ∀ X0 X1 X2 : G, (k (τ X0) (M.op X1 X2)) = (M.op (τ X0) (M.op X1 X2)) ∨ (M.op X2 X2) = (k X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq690485 X0 X1 X2
       have i₂ := eq22 X0 (M.op X1 X2)
       grind)
    | exact superpose eq22 eq690485
    | (have j0 := eq690485 X0 X1 X2
       grind)
    | exact resolve eq690485 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq690485
  have eq691126 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X1 X2)) ∨ (k X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq690763 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq690763
    | (have j0 := eq690763 X0 X1 X2
       grind)
    | exact resolve eq690763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690763
  have eq692669 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq691126 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691126
  have eq692672 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq692669 X0 X1
       have j1 := eq647852 X0 X1 X0 x
       grind)
    | (have r₁ := eq692669 x X1
       have r₂ := eq647852 X0 X1 x x
       grind)
    | exact resolve eq692669 eq647852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647852 eq692669
  have eq693198 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq692672 (σ X0) (σ X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq692672
    | exact resolve eq692672 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693264 : ∀ X0 : G, (k (τ X0) (τ (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq692672 (τ X0) (τ X0)
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq692672
    | exact resolve eq692672 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq693717 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq693264 X0
       have i₂ := eq31 (M.op X0 X0) X0
       grind)
    | exact superpose eq31 eq693264
    | exact resolve eq693264 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq693264
  have eq693754 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq693198 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq693198
    | exact resolve eq693198 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693198
  have eq693772 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq693717 X0
       have i₂ := eq692672 X0 X0
       grind)
    | exact superpose eq692672 eq693717
    | exact resolve eq693717 eq692672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693717
  have eq693778 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq693754 X0
       have i₂ := eq692672 X0 X0
       grind)
    | exact superpose eq692672 eq693754
    | exact resolve eq693754 eq692672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692672 eq693754
  have eq694171 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq693772 (M.op X0 X0)
       grind)
    | exact superpose eq693772 eq116
    | exact resolve eq116 eq693772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq694175 : ∀ X0 : G, (k (σ (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))) X0) = (σ (M.op (τ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq21330 X0 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq693772 (M.op X0 X0)
       grind)
    | exact superpose eq693772 eq21330
    | exact resolve eq21330 eq693772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21330 eq693772
  have eq694469 : ∀ X0 : G, (σ (M.op (τ (M.op (M.op X0 X0) X0)) (τ X0))) = (k (σ (τ (M.op (M.op X0 X0) X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq694175 x
       have i₂ := eq9 (M.op x x) x x
       grind)
    | exact superpose eq9 eq694175
    | exact resolve eq694175 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694175
  have eq694473 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq694171 X0 X1
       have i₂ := eq9 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq9 eq694171
    | exact resolve eq694171 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694171
  have eq694739 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = (σ (M.op (τ (M.op (M.op X0 X0) X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq694469 X0
       have i₂ := eq11 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq11 eq694469
    | exact resolve eq694469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694469
  have eq694877 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (σ (M.op (τ (M.op (M.op X0 X0) X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq694739 X0
       have i₂ := eq20310 X0 X0 X0
       grind)
    | exact superpose eq20310 eq694739
    | exact resolve eq694739 eq20310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694739
  have eq695123 : ∀ X0 X1 : G, (M.op X1 (τ (σ X0))) = (M.op X1 (τ (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq694473 (σ X0) X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq694473
    | exact resolve eq694473 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq695490 : ∀ X0 X1 : G, (σ (M.op (τ (M.op (M.op X0 X0) X0)) (τ X0))) ≠ (M.op (σ (τ (M.op (M.op X0 X0) X0))) (σ X1)) ∨ (k X1 (τ (M.op (M.op X0 X0) X0))) = (τ (M.op (σ X1) (σ (τ (M.op (M.op X0 X0) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1125 X1 (τ (M.op (M.op X0 X0) X0))
       have i₂ := eq694473 X0 (τ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq694473 eq1125
    | (have j0 := eq1125 X1 (τ (M.op (M.op X0 X0) X0))
       grind)
    | exact resolve eq1125 eq694473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq694473
  have eq696491 : ∀ X0 X1 : G, (σ (M.op (τ (M.op (M.op X0 X0) X0)) (τ X0))) ≠ (M.op (M.op (M.op X0 X0) X0) (σ X1)) ∨ (k X1 (τ (M.op (M.op X0 X0) X0))) = (τ (M.op (σ X1) (σ (τ (M.op (M.op X0 X0) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq695490 X0 X1
       have i₂ := eq11 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq11 eq695490
    | (have j0 := eq695490 X0 X1
       grind)
    | exact resolve eq695490 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695490
  have eq696732 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (τ (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq695123 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq695123
    | exact resolve eq695123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695123
  have eq696975 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X0) ≠ (M.op (M.op (M.op X0 X0) X0) (σ X1)) ∨ (k X1 (τ (M.op (M.op X0 X0) X0))) = (τ (M.op (σ X1) (σ (τ (M.op (M.op X0 X0) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq696491 X0 X1
       have i₂ := eq694877 X0
       grind)
    | exact superpose eq694877 eq696491
    | (have j0 := eq696491 X0 X1
       grind)
    | (have r₁ := eq696491 (σ X1) X1
       have r₂ := eq694877 (σ X1)
       grind)
    | exact resolve eq696491 eq694877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694877 eq696491
  have eq697275 : ∀ X0 X1 : G, (k X1 (τ (M.op (M.op X0 X0) X0))) = (τ (M.op (σ X1) (M.op (M.op X0 X0) X0))) ∨ (M.op (M.op (M.op X0 X0) X0) X0) ≠ (M.op (M.op (M.op X0 X0) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq696975 X0 X1
       have i₂ := eq11 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq11 eq696975
    | (have j0 := eq696975 X0 X1
       grind)
    | exact resolve eq696975 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696975
  have eq697485 : ∀ X0 X1 : G, (τ (M.op (σ X1) X0)) = (k X1 (τ (M.op (M.op X0 X0) X0))) ∨ (M.op (M.op (M.op X0 X0) X0) X0) ≠ (M.op (M.op (M.op X0 X0) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq697275 X0 X1
       have i₂ := eq63 X0 X0 (σ X1) X0
       grind)
    | exact superpose eq63 eq697275
    | (have j0 := eq697275 X0 X1
       grind)
    | (have r₁ := eq697275 (M.op (M.op x (σ X1)) X0) X1
       have r₂ := eq63 X0 (σ X1) (M.op (M.op (M.op (M.op x (σ X1)) X0) (M.op (M.op x (σ X1)) X0)) (M.op (M.op x (σ X1)) X0)) x
       grind)
    | exact resolve eq697275 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697275
  have eq697624 : ∀ X0 X1 : G, (τ (M.op (σ X1) X0)) = (k X1 (τ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq697485 X0 X1
       have j1 := eq18766 X1 X0 X0 X0 x
       grind)
    | (have r₁ := eq697485 x X0
       have r₂ := eq18766 X0 X1 x x (M.op (M.op x x) x)
       grind)
    | (have r₁ := eq697485 (σ X0) X1
       have r₂ := eq18766 X0 X1 x (σ X1) (M.op (M.op (σ X0) (σ X0)) (σ X0))
       grind)
    | exact resolve eq697485 eq18766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18766 eq697485
  have eq698176 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq693778 (M.op X0 X0)
       grind)
    | exact superpose eq693778 eq106
    | exact resolve eq106 eq693778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq698181 : ∀ X0 : G, (k (τ (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))))) X0) = (τ (M.op (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq20724 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq693778 (M.op X0 X0)
       grind)
    | exact superpose eq693778 eq20724
    | exact resolve eq20724 eq693778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20724
  have eq698247 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq129 X0 (σ (M.op X0 X0))
       have i₂ := eq693778 (M.op X0 X0)
       grind)
    | exact superpose eq693778 eq129
    | exact resolve eq129 eq693778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq693778
  have eq698451 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq698247 X0
       have i₂ := eq9 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq9 eq698247
    | exact resolve eq698247 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698247
  have eq698510 : ∀ X0 : G, (τ (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0))) = (k (τ (σ (M.op (M.op X0 X0) X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq698181 x
       have i₂ := eq9 (M.op x x) x x
       grind)
    | exact superpose eq9 eq698181
    | exact resolve eq698181 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698181
  have eq698515 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq698176 X0 X1
       have i₂ := eq9 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq9 eq698176
    | exact resolve eq698176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698176
  have eq698831 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = (τ (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq698510 X0
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq698510
    | exact resolve eq698510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698510
  have eq698991 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (τ (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq698831 X0
       have i₂ := eq20310 X0 X0 X0
       grind)
    | exact superpose eq20310 eq698831
    | exact resolve eq698831 eq20310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698831
  have eq703948 : ∀ X0 X1 : G, (k (τ (M.op (σ (M.op (M.op X0 X0) X0)) X1)) X0) = (τ (M.op (M.op (σ (M.op (M.op X0 X0) X0)) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20522 (σ (M.op X0 X0)) X0 x
       have i₂ := eq698451 X0
       grind)
    | exact superpose eq698451 eq20522
    | exact resolve eq20522 eq698451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20522
  have eq709084 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ (M.op (M.op X0 X0) X0)))) = (k X1 (τ (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq697624 (σ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq698515 X0 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq698515 eq697624
    | exact resolve eq697624 eq698515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709563 : ∀ X0 X1 : G, (σ (τ (M.op (σ (τ X0)) X1))) = (k X0 (σ (τ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ (M.op (M.op X1 X1) X1))
       have i₂ := eq697624 X1 (τ X0)
       grind)
    | exact superpose eq697624 eq17
    | exact resolve eq17 eq697624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq697624
  have eq709929 : ∀ X0 X1 : G, (σ (τ (M.op (σ (τ X0)) X1))) = (k X0 (M.op (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq709563 X0 X1
       have i₂ := eq11 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq11 eq709563
    | exact resolve eq709563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709563
  have eq710373 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ (M.op (M.op X0 X0) X0)))) = (k X1 (k (τ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq709084 X0 X1
       have i₂ := eq703948 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq703948 eq709084
    | exact resolve eq709084 eq703948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703948 eq709084
  have eq710654 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (k X0 (M.op (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq709929 X0 X1
       have i₂ := eq11 (M.op (σ (τ X0)) X1)
       grind)
    | exact superpose eq11 eq709929
    | exact resolve eq709929 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709929
  have eq710935 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ (M.op (M.op X0 X0) X0)))) = (k X1 (k (τ (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq710373 X0 X1
       have i₂ := eq698515 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq698515 eq710373
    | exact resolve eq710373 eq698515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710373
  have eq711174 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq710654 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq710654
    | exact resolve eq710654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710654
  have eq711335 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ (M.op (M.op X0 X0) X0)))) = (k X1 (k (M.op (M.op (M.op X0 X0) X0) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq710935 X0 X1
       have i₂ := eq698991 X0
       grind)
    | exact superpose eq698991 eq710935
    | exact resolve eq710935 eq698991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698991 eq710935
  have eq711550 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ (M.op (M.op X0 X0) X0)))) = (k X1 (M.op (M.op (M.op (M.op X0 X0) X0) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq711335 X0 X1
       have i₂ := eq20310 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq20310 eq711335
    | exact resolve eq711335 eq20310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20310 eq711335
  have eq711672 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ X0))) = (k X1 (M.op (M.op (M.op (M.op X0 X0) X0) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq711550 X0 X1
       have i₂ := eq698515 X0 (σ X1)
       grind)
    | exact superpose eq698515 eq711550
    | exact resolve eq711550 eq698515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698515 eq711550
  have eq712030 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ (M.op X0 X0)) (σ X0)))) = (k X1 (M.op (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) (τ (M.op (σ (M.op X0 X0)) (σ X0)))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq711174 X1 (τ (M.op (σ (M.op X0 X0)) (σ X0)))
       have i₂ := eq696732 X0 (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) (τ (M.op (σ (M.op X0 X0)) (σ X0))))
       grind)
    | exact superpose eq696732 eq711174
    | exact resolve eq711174 eq696732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711174
  have eq712855 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ (M.op X0 X0)) (σ X0)))) = (k X1 (M.op (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq712030 X0 X1
       have i₂ := eq696732 X0 (τ (M.op (σ (M.op X0 X0)) (σ X0)))
       grind)
    | exact superpose eq696732 eq712030
    | exact resolve eq712030 eq696732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696732 eq712030
  have eq713149 : ∀ X0 X1 : G, (M.op X1 (τ (σ (M.op (M.op X0 X0) X0)))) = (k X1 (M.op (M.op (τ (σ (M.op (M.op X0 X0) X0))) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq712855 X0 X1
       have i₂ := eq698451 X0
       grind)
    | exact superpose eq698451 eq712855
    | exact resolve eq712855 eq698451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698451 eq712855
  have eq713327 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = (k X1 (M.op (M.op (M.op (M.op X0 X0) X0) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq713149 X0 X1
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq713149
    | exact resolve eq713149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713149
  have eq713430 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ X0))) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq713327 X0 X1
       have i₂ := eq711672 X0 X1
       grind)
    | exact superpose eq711672 eq713327
    | exact resolve eq713327 eq711672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711672 eq713327
  have eq713509 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq713430 X0 X1
       have i₂ := eq63 X0 X0 X1 X0
       grind)
    | exact superpose eq63 eq713430
    | exact resolve eq713430 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq713430
  have eq714081 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq713509 X1 X0
       grind)
    | exact superpose eq713509 eq11
    | exact resolve eq11 eq713509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713509
  have eq719578 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq714081 x y
       grind)
    | exact superpose eq714081 eq16
    | (have r₁ := eq16
       have r₂ := eq714081 x y
       grind)
    | exact resolve eq16 eq714081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714081
  have eq720067 : False := by grind
  exact eq720067

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq202 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1048 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq209 (τ X1) (τ X0)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq209
    | (have j0 := eq209 (τ X1) (τ X0)
       grind)
    | exact resolve eq209 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1048 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1048
    | (have j0 := eq1048 X0 X1
       grind)
    | exact resolve eq1048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1072 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1065
    | (have j0 := eq1065 X0 X1
       grind)
    | exact resolve eq1065 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1078 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1072 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1072
    | (have j0 := eq1072 X0 X1
       grind)
    | exact resolve eq1072 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1083 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1078 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1078
    | (have j0 := eq1078 X0 X1
       grind)
    | exact resolve eq1078 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1086 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1083 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1083
    | (have j0 := eq1083 X0 X1
       grind)
    | exact resolve eq1083 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1087 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1086 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1086
    | (have j0 := eq1086 X0 X1
       grind)
    | exact resolve eq1086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq2833 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq83 X1 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq83 X0 (σ X0)
       grind)
    | (have r₁ := eq13 (M.op (σ X0) (σ X0)) X1
       have r₂ := eq83 X0 (M.op X1 (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2845 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq83 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2846 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2845 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2847 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2833 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2833
  have eq2848 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2847 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847
  have eq2851 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2846 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2846
    | (have j0 := eq2846 X0
       grind)
    | exact resolve eq2846 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq2884 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq2851 X0
       grind)
    | exact superpose eq2851 eq40
    | (have j1 := eq2851 X0
       grind)
    | exact resolve eq40 eq2851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2851
  have eq2898 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2884 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2884
    | (have j0 := eq2884 X0
       grind)
    | exact resolve eq2884 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884
  have eq2899 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2898 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2898
  have eq2901 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2899 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2899
    | exact resolve eq2899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2923 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq2899 X0
       grind)
    | exact superpose eq2899 eq11
    | exact resolve eq11 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2964 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2901 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq2901
    | exact resolve eq2901 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2901
  have eq3057 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2964 X0
       grind)
    | exact superpose eq2964 eq11
    | exact resolve eq11 eq2964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3130 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3057 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3057
    | exact resolve eq3057 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057
  have eq3187 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq3130 (τ X0)
       grind)
    | exact superpose eq3130 eq36
    | exact resolve eq36 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3235 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3187 X0
       have i₂ := eq2964 X0
       grind)
    | exact superpose eq2964 eq3187
    | exact resolve eq3187 eq2964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964 eq3187
  have eq3732 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq3750 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3732 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq3732
    | exact resolve eq3732 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq3780 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3750 X0
       have i₂ := eq3130 X0
       grind)
    | exact superpose eq3130 eq3750
    | exact resolve eq3750 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750
  have eq3795 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq3780
  have eq345955 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2848 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2848
    | exact resolve eq2848 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346105 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X1)
       have i₂ := eq2848 (σ X0) X1
       grind)
    | exact superpose eq2848 eq32
    | (have j1 := eq2848 (σ X0) X1
       grind)
    | exact resolve eq32 eq2848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2848
  have eq346271 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq346105 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq346105
    | (have j0 := eq346105 X0 X1
       grind)
    | exact resolve eq346105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346105
  have eq346375 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq345955 X0 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq345955
    | (have j0 := eq345955 X0 X1
       grind)
    | exact resolve eq345955 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345955
  have eq346437 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq346271 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq346271
    | (have j0 := eq346271 X0 X1
       grind)
    | exact resolve eq346271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346271
  have eq346590 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq346437 X0 X1
       have i₂ := eq2923 X1
       grind)
    | exact superpose eq2923 eq346437
    | (have j0 := eq346437 X0 X1
       grind)
    | exact resolve eq346437 eq2923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346437
  have eq346719 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq346590 X0 X1
       have i₂ := eq3130 X1
       grind)
    | exact superpose eq3130 eq346590
    | (have j0 := eq346590 X0 X1
       grind)
    | exact resolve eq346590 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346590
  have eq346815 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq346719 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq346719
    | (have j0 := eq346719 X0 X1
       grind)
    | exact resolve eq346719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346719
  have eq347230 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq346375 X0 X1
       grind)
    | exact superpose eq346375 eq11
    | (have j1 := eq346375 X0 X1
       grind)
    | exact resolve eq11 eq346375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346375
  have eq347481 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq347230 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq347230
    | (have j0 := eq347230 X0 X1
       grind)
    | exact resolve eq347230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347230
  have eq348814 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq347481 (τ X0) X1
       grind)
    | exact superpose eq347481 eq19
    | (have j1 := eq347481 (τ X0) X1
       grind)
    | exact resolve eq19 eq347481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq347481
  have eq349176 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq348814 X0 X1
       have i₂ := eq3235 X0
       grind)
    | exact superpose eq3235 eq348814
    | (have j0 := eq348814 X0 X1
       grind)
    | exact resolve eq348814 eq3235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348814
  have eq349771 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq346815 (τ X1) (τ X0)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq346815
    | (have j0 := eq346815 (τ X0) (τ X1)
       grind)
    | exact resolve eq346815 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq346815
  have eq350312 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq349771 X0 X1
       have i₂ := eq3235 X1
       grind)
    | exact superpose eq3235 eq349771
    | (have j0 := eq349771 X0 X1
       grind)
    | exact resolve eq349771 eq3235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235 eq349771
  have eq350540 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq350312 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq350312
    | (have j0 := eq350312 X0 X1
       grind)
    | exact resolve eq350312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350312
  have eq350740 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq350540 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350540
    | (have j0 := eq350540 X0 X1
       grind)
    | exact resolve eq350540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350540
  have eq350892 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq350740 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350740
    | (have j0 := eq350740 X0 X1
       grind)
    | exact resolve eq350740 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350740
  have eq350996 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq350892 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq350892
    | (have j0 := eq350892 X0 X1
       grind)
    | exact resolve eq350892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350892
  have eq351964 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq350996 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350996
  have eq360769 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq349176 X1 (τ X0)
       grind)
    | exact superpose eq349176 eq18
    | (have j1 := eq349176 X1 (τ X0)
       grind)
    | exact resolve eq18 eq349176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq349176
  have eq360904 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq360769 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq360769
    | (have j0 := eq360769 X0 X1
       grind)
    | exact resolve eq360769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360769
  have eq361057 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq360904 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq360904
    | (have j0 := eq360904 X0 X1
       grind)
    | exact resolve eq360904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360904
  have eq361193 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq361057 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq361057
    | (have j0 := eq361057 X0 X1
       grind)
    | exact resolve eq361057 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361057
  have eq373015 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq361193 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq361193
    | (have j0 := eq361193 X1 (σ X0)
       grind)
    | exact resolve eq361193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361193
  have eq373518 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq373015 X0 X1
       have i₂ := eq2899 X0
       grind)
    | exact superpose eq2899 eq373015
    | (have j0 := eq373015 X0 X1
       grind)
    | exact resolve eq373015 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899 eq373015
  have eq373649 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq373518 X0 X1
       have i₂ := eq3130 X0
       grind)
    | exact superpose eq3130 eq373518
    | (have j0 := eq373518 X0 X1
       grind)
    | exact resolve eq373518 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373518
  have eq382157 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq373649 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq373649
    | (have j0 := eq373649 X1 (σ X0)
       grind)
    | exact resolve eq373649 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373649
  have eq382513 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq382157 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq382157
    | (have j0 := eq382157 X0 X1
       grind)
    | exact resolve eq382157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382157
  have eq382696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq382513 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq382513
    | (have j0 := eq382513 X0 X1
       grind)
    | exact resolve eq382513 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382513
  have eq383491 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq202
       have i₂ := eq382696 y x
       grind)
    | exact superpose eq382696 eq202
    | (have j1 := eq382696 y x
       grind)
    | (have r₁ := eq202
       have r₂ := eq382696 y x
       grind)
    | exact resolve eq202 eq382696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq382696
  have eq383656 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq383491
  have eq383766 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq209 x y
       grind)
    | (have r₁ := eq383656
       have r₂ := eq209 x y
       grind)
    | exact resolve eq383656 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq383656
  have eq383961 : (σ y) = (σ (k x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq383766
       have i₂ := eq2923 x
       grind)
    | exact superpose eq2923 eq383766
    | exact resolve eq383766 eq2923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383766
  have eq384095 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq383961
       have i₂ := eq3130 x
       grind)
    | exact superpose eq3130 eq383961
    | exact resolve eq383961 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383961
  have eq386265 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq384095
       grind)
    | exact superpose eq384095 eq16
    | exact resolve eq16 eq384095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386315 : (τ (σ y)) ≠ (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq351964 (σ y) (σ x)
       have i₂ := eq384095
       grind)
    | exact superpose eq384095 eq351964
    | (have j0 := eq351964 (σ y) (σ x)
       grind)
    | exact resolve eq351964 eq384095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351964 eq384095
  have eq386318 : (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq386315
  have eq386323 : (σ y) = (σ (k x x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq386318
       have i₂ := eq2923 x
       grind)
    | exact superpose eq2923 eq386318
    | exact resolve eq386318 eq2923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923 eq386318
  have eq386357 : (σ y) = (σ (M.op x x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq386323
       have i₂ := eq3130 x
       grind)
    | exact superpose eq3130 eq386323
    | exact resolve eq386323 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130 eq386323
  have eq386358 : (σ y) = (σ (M.op x x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x x) := by grind
  clear eq386357
  have eq386384 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq386358
       have i₂ := eq26 (σ y) x
       grind)
    | exact superpose eq26 eq386358
    | exact resolve eq386358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq386358
  have eq386403 : y = (k y x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq386384
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq386384
    | exact resolve eq386384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386384
  have eq387560 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1087 y x
       have i₂ := eq386403
       grind)
    | exact superpose eq386403 eq1087
    | (have j0 := eq1087 y x
       grind)
    | (have r₁ := eq1087 y x
       have r₂ := eq386403
       grind)
    | exact resolve eq1087 eq386403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087 eq386403
  have eq387585 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq387560
  have eq387586 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq387585
  have eq388780 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq386265
       have i₂ := eq387586
       grind)
    | exact superpose eq387586 eq386265
    | exact resolve eq386265 eq387586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386265 eq387586
  have eq388781 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq388780
  have eq388782 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq388781
  have eq388800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3795 x
       have i₂ := eq388782
       grind)
    | exact superpose eq388782 eq3795
    | exact resolve eq3795 eq388782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388782
  have eq388970 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq388800
       have r₂ := eq16
       grind)
    | exact resolve eq388800 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388800
  have eq390184 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq388970
       grind)
    | exact superpose eq388970 eq10
    | exact resolve eq10 eq388970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388970
  have eq390486 : y = (M.op x x) := by
    first
    | (have i₁ := eq390184
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq390184
    | exact resolve eq390184 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390184
  have eq390717 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3795 x
       have i₂ := eq390486
       grind)
    | exact superpose eq390486 eq3795
    | exact resolve eq3795 eq390486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3795 eq390486
  have eq390908 : False := by grind
  exact eq390908

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X2 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq29 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq130 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq235 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq236 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq235 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq241 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq236 X0 X1
       have j1 := eq130 X0 X1
       grind)
    | (have r₁ := eq236 X0 X1
       have r₂ := eq130 X0 X1
       grind)
    | (have r₁ := eq236 X1 X1
       have r₂ := eq130 X1 X1
       grind)
    | exact resolve eq236 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq236
  have eq374 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq241 (σ X1) (σ X0)
       grind)
    | exact superpose eq241 eq15
    | exact resolve eq15 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq241 X1 X0
       grind)
    | exact superpose eq241 eq374
    | exact resolve eq374 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq374
  have eq384 : False := by grind
  exact eq384
