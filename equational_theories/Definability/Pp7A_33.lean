import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2477`: `x = (x ◇ ((y ◇ z) ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_x_pyx_Equation2477 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2477 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2477.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) X0)) x) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X0 (M.op (M.op X2 X3) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 (M.op (M.op X2 X3) X0)) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X1 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 y x
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ y) (σ x)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X0)) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X0 (M.op (M.op X1 X2) X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (M.op X0 (M.op x X0)) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) X0)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq53 X1 X1
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X0 (M.op (M.op X1 X2) X0)) = (M.op X1 (M.op X0 (M.op (M.op X1 X2) X0))) ∨ (M.op X0 (M.op (M.op X1 X2) X0)) = (k (M.op X0 (M.op (M.op X1 X2) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X0 (M.op (M.op X1 X2) X0)) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X0 X2) X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq82 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq92 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq94 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq118
  have eq130 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
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
  have eq167 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq143 eq16
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq278 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq34
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq400 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq60 eq53
    | exact resolve eq53 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq408 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq62 eq53
    | exact resolve eq53 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq608 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x X1)) (M.op x X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq624 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op x X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq608 X0 X1
       have i₂ := eq400 X1
       grind)
    | (have i₁ := eq608 X0 y
       have i₂ := eq400 y
       grind)
    | exact superpose eq400 eq608
    | exact resolve eq608 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq807 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq814 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq807 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq816 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq814 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq814 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq814 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq814 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq826 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq816 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq816
    | (have j0 := eq816 X0 X1
       grind)
    | exact resolve eq816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq927 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op X0 (M.op X0 (M.op (M.op X0 X1) X0))) ∨ (M.op X0 (M.op (M.op X0 X1) X0)) = (k (M.op X0 (M.op (M.op X0 X1) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1133 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 X2) X2
       have i₂ := eq53 X2 X0
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1163 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) (M.op (M.op X3 X4) (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 X2) X0 X3 X4
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1200 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1163 X0 X1 X2 X3 x
       have i₂ := eq56 (M.op X1 X2) X3 x
       grind)
    | exact superpose eq56 eq1163
    | exact resolve eq1163 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1829 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq1200
    | exact resolve eq1200 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq2215 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2263 : (M.op (M.op x (M.op x y)) x) = (k (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq624 eq2215
    | exact resolve eq2215 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq4305 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq94 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94
    | (have j0 := eq94 x
       grind)
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq4334 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4305
  have eq4344 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4334
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4334
    | exact resolve eq4334 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq4354 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4344
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq4344 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4344
  have eq4427 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq4452 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4427
  have eq4459 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4452
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq4452
    | exact resolve eq4452 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq4452
  have eq4471 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4459
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4459 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459
  have eq4543 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq144
    | (have j0 := eq144 (M.op x y)
       grind)
    | exact resolve eq144 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq4567 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq4543
  have eq4573 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq143 eq4567
    | exact resolve eq4567 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4567
  have eq4587 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq4573
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4573 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4573
  have eq4598 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq4587 eq167
    | exact resolve eq167 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq5149 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq278
    | exact resolve eq278 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq5205 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5149 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq5149
    | (have j0 := eq5149 X0 X1
       grind)
    | exact resolve eq5149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq6839 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op (M.op X0 X1) X0)) = (k (M.op X0 (M.op (M.op X0 X1) X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq927 X0 X1
       have i₂ := eq1133 X0 X0 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq1133 eq927
    | (have j0 := eq927 X0 X1
       grind)
    | exact resolve eq927 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq1133
  have eq6840 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op (M.op X0 X1) X0)) = (k (M.op X0 (M.op (M.op X0 X1) X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6839 X0 X1
       have i₂ := eq56 X0 X0 X1
       grind)
    | exact superpose eq56 eq6839
    | (have j0 := eq6839 X0 X1
       grind)
    | exact resolve eq6839 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6839
  have eq6841 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6840 x x
       have i₂ := eq56 x x x
       grind)
    | exact superpose eq56 eq6840
    | (have j0 := eq6840 X0 x
       grind)
    | exact resolve eq6840 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq6840
  have eq8529 : (σ (k (k x x) x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq4354 eq170
    | exact resolve eq170 eq4354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq13226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13226
    | exact resolve eq13226 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13226
  have eq13239 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq13233
       have r₂ := eq27
       grind)
    | exact resolve eq13233 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13233
  have eq13241 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13239
    | exact resolve eq13239 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13239
  have eq13249 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13241 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13241
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13241
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13241
       grind)
    | exact resolve eq12 eq13241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13241
  have eq13273 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq13249
  have eq13286 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13273
    | exact resolve eq13273 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13273
  have eq13287 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq13286
  have eq13375 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13287 eq117
    | exact resolve eq117 eq13287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13379 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13287 eq114
    | exact resolve eq114 eq13287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq13287
  have eq13391 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13375
  have eq13394 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq13379
    | exact resolve eq13379 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13379
  have eq13404 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13391
       grind)
    | exact superpose eq13391 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13391
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13391
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13391
       grind)
    | exact resolve eq12 eq13391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13405 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq13391
       grind)
    | exact superpose eq13391 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13391
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13391
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13391
       grind)
    | exact resolve eq13 eq13391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13391
  have eq13427 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13405
  have eq13428 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13404
  have eq13440 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13427
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13427
    | exact resolve eq13427 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13427
  have eq13441 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13428
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13428
    | exact resolve eq13428 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13428
  have eq13442 : y = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13441
  have eq13452 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4471 eq124
    | exact resolve eq124 eq4471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq4471
  have eq13627 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq13440
       grind)
    | exact superpose eq13440 eq44
    | exact resolve eq44 eq13440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13440
  have eq13653 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13627
    | exact resolve eq13627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13627
  have eq13714 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq812 x y
       have i₂ := eq13442
       grind)
    | exact superpose eq13442 eq812
    | (have j0 := eq812 x y
       grind)
    | exact resolve eq812 eq13442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13442
  have eq13720 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13714
  have eq13726 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13720
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13720
    | exact resolve eq13720 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13720
  have eq13739 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13726
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13726
    | exact resolve eq13726 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13726
  have eq13747 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13739
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13739
    | exact resolve eq13739 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13739
  have eq13753 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13747
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13747
    | exact resolve eq13747 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13747
  have eq13758 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13753
    | exact resolve eq13753 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13753
  have eq13759 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13758
  have eq14501 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13759 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13759
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13759
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13759
       grind)
    | exact resolve eq13 eq13759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13759
  have eq14523 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14501
  have eq14536 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq14523
    | exact resolve eq14523 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14523
  have eq14616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14536 eq13653
    | exact resolve eq13653 eq14536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13653 eq14536
  have eq14624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14616
  have eq14626 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14624
       have r₂ := eq27
       grind)
    | exact resolve eq14624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14624
  have eq20156 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq13394
       grind)
    | exact superpose eq13394 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq13394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13394
  have eq20166 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20156
  have eq20174 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20166
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20166
    | exact resolve eq20166 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20166
  have eq20175 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20174
  have eq20213 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq20175
       grind)
    | exact superpose eq20175 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20175
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20175
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20175
       grind)
    | exact resolve eq12 eq20175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20214 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20175
       grind)
    | exact superpose eq20175 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20175
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20175
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20175
       grind)
    | exact resolve eq13 eq20175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20175
  have eq20236 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20214
  have eq20237 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20213
  have eq20249 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20236
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20236
    | exact resolve eq20236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20236
  have eq20250 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20237
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20237
    | exact resolve eq20237 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20237
  have eq20251 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20250
  have eq20323 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20249
       grind)
    | exact superpose eq20249 eq44
    | exact resolve eq44 eq20249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20249
  have eq20353 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20323
    | exact resolve eq20323 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20323
  have eq20416 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq812 x y
       have i₂ := eq20251
       grind)
    | exact superpose eq20251 eq812
    | (have j0 := eq812 x y
       grind)
    | exact resolve eq812 eq20251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq20418 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq826 y x
       have i₂ := eq20251
       grind)
    | exact superpose eq20251 eq826
    | (have j0 := eq826 y x
       grind)
    | exact resolve eq826 eq20251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq20251
  have eq20420 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20418
  have eq20422 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20416
  have eq20426 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20420
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq20420
    | exact resolve eq20420 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20420
  have eq20428 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20422
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20422
    | exact resolve eq20422 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20422
  have eq20441 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20426
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20426
    | exact resolve eq20426 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20426
  have eq20443 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20428
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20428
    | exact resolve eq20428 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20428
  have eq20449 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20441
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20441
    | exact resolve eq20441 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20441
  have eq20451 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20443
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20443
    | exact resolve eq20443 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20443
  have eq20455 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20449
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20449
    | exact resolve eq20449 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20449
  have eq20457 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20451
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20451
    | exact resolve eq20451 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20451
  have eq20461 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20455
       have r₂ := eq82
       grind)
    | exact resolve eq20455 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq20455
  have eq20462 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq20457
    | exact resolve eq20457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20457
  have eq20463 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20462
  have eq21281 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20463 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20463
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20463
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20463
       grind)
    | exact resolve eq13 eq20463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20463
  have eq21303 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21281
  have eq21326 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq21303
    | exact resolve eq21303 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21303
  have eq22232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21326 eq20353
    | exact resolve eq20353 eq21326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20353 eq21326
  have eq22240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22232
  have eq22246 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22240
       have r₂ := eq27
       grind)
    | exact resolve eq22240 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22240
  have eq22455 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22246 eq27
    | exact resolve eq27 eq22246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22459 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22246 eq67
    | (have r₁ := eq67
       have r₂ := eq22246
       grind)
    | exact resolve eq67 eq22246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq22496 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq22459
  have eq23803 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22496 eq117
    | exact resolve eq117 eq22496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq22496
  have eq23845 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq23803
  have eq37022 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20461 eq72
    | exact resolve eq72 eq20461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq20461
  have eq37076 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq37022
    | exact resolve eq37022 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37022
  have eq38058 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37076 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq37076
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq37076
       grind)
    | exact resolve eq13 eq37076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38080 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq38058
  have eq38112 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq38080
    | exact resolve eq38080 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38080
  have eq40239 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq23845 eq37076
    | exact resolve eq37076 eq23845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23845 eq37076
  have eq40313 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq40239
  have eq40346 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq40313
       have r₂ := eq80
       grind)
    | exact resolve eq40313 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq40313
  have eq42207 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq40346
       grind)
    | exact superpose eq40346 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq40346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40346
  have eq42217 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq42207
  have eq42225 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq42217
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42217
    | exact resolve eq42217 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42217
  have eq42278 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq42225
       grind)
    | exact superpose eq42225 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq42225
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq42225
       grind)
    | exact resolve eq13 eq42225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42225
  have eq42300 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq42278
  have eq42313 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq42300
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42300
    | exact resolve eq42300 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42300
  have eq42864 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq42313
       grind)
    | exact superpose eq42313 eq44
    | exact resolve eq44 eq42313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq42897 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq42864
    | exact resolve eq42864 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42864
  have eq44270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq42897 eq38112
    | exact resolve eq38112 eq42897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38112 eq42897
  have eq44282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq44270
  have eq44294 : x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq44282
       have r₂ := eq27
       grind)
    | exact resolve eq44282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44282
  have eq45255 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq42313
       have i₂ := eq44294
       grind)
    | exact superpose eq44294 eq42313
    | exact resolve eq42313 eq44294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42313 eq44294
  have eq45267 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq45255
  have eq45548 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45267 eq28
    | exact resolve eq28 eq45267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq45267
  have eq45828 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq45548
    | exact resolve eq45548 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45548
  have eq45829 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq45828
  have eq45836 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45829 eq20
    | exact resolve eq20 eq45829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45839 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45829 eq54
    | exact resolve eq54 eq45829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45953 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq45829
  have eq46058 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45836
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45836
    | exact resolve eq45836 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45836
  have eq46465 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13452
       have i₂ := eq45839
       grind)
    | exact superpose eq45839 eq13452
    | exact resolve eq13452 eq45839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13452 eq45839
  have eq46509 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq46465
       have r₂ := eq45953
       grind)
    | exact resolve eq46465 eq45953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45953 eq46465
  have eq46510 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46509
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46509
    | exact resolve eq46509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46509
  have eq47730 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq46510 eq1200
    | exact resolve eq1200 eq46510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200 eq46510
  have eq47744 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1829 eq47730
    | exact resolve eq47730 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829 eq47730
  have eq47759 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47744 eq27
    | exact resolve eq27 eq47744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47744
  have eq47814 : x = (M.op x y) := by
    first
    | (have r₁ := eq47759
       have r₂ := eq46058
       grind)
    | exact resolve eq47759 eq46058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46058 eq47759
  have eq48058 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq47814 eq20
    | exact resolve eq20 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq48129 : (k (M.op x x) x) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq47814 eq2263
    | exact resolve eq2263 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq48238 : x = (k (M.op x x) x) := by
    first
    | (have i₁ := eq48129
       have i₂ := eq53 x x
       grind)
    | exact superpose eq53 eq48129
    | exact resolve eq48129 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48129
  have eq48301 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq48058
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48058
    | exact resolve eq48058 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48058
  have eq48319 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq48301 eq26
    | exact resolve eq26 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48344 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq48301 eq408
    | exact resolve eq408 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq90577 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq143
       have i₂ := eq5205 sF0 sF0
       grind)
    | exact superpose eq5205 eq143
    | (have j1 := eq5205 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq143 eq5205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq5205
  have eq90680 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq90577
  have eq90785 : (σ (M.op x x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq47814 eq90680
    | exact resolve eq90680 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90680
  have eq91154 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4587 eq90785
    | exact resolve eq90785 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587 eq90785
  have eq91387 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq47814 eq91154
    | exact resolve eq91154 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91154
  have eq91906 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq91387
       grind)
    | exact superpose eq91387 eq16
    | exact resolve eq16 eq91387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91387
  have eq92050 : (M.op x x) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4598 eq91906
    | exact resolve eq91906 eq4598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91906
  have eq92071 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq47814 eq92050
    | exact resolve eq92050 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92050
  have eq92084 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq92071
       have r₂ := eq13 x x
       grind)
    | exact resolve eq92071 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92071
  have eq92103 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq92084
       grind)
    | exact superpose eq92084 eq43
    | exact resolve eq43 eq92084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq92107 : (k (M.op (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) := by
    first
    | (have i₁ := eq8529
       have i₂ := eq92084
       grind)
    | exact superpose eq92084 eq8529
    | exact resolve eq8529 eq92084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8529
  have eq92145 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq92107
       have i₂ := eq48238
       grind)
    | exact superpose eq48238 eq92107
    | exact resolve eq92107 eq48238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48238 eq92107
  have eq92149 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4354 eq92103
    | exact resolve eq92103 eq4354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4354 eq92103
  have eq92160 : (σ x) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq48301 eq92145
    | exact resolve eq92145 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92145
  have eq92163 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq48301 eq92149
    | exact resolve eq92149 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92149
  have eq92172 : (σ x) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq92160
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92160
    | exact resolve eq92160 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92160
  have eq92184 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq48301 eq92172
    | exact resolve eq92172 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92172
  have eq92220 : (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq37 (M.op x x)
       have i₂ := eq92163
       grind)
    | exact superpose eq92163 eq37
    | exact resolve eq37 eq92163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq92357 : (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k x (M.op x x))) := by
    first
    | exact superpose eq47814 eq92220
    | exact resolve eq92220 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92220
  have eq92382 : (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq92357
       have i₂ := eq2215 x
       grind)
    | exact superpose eq2215 eq92357
    | exact resolve eq92357 eq2215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92357
  have eq92395 : (σ (M.op x (M.op x y))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq92382
       have i₂ := eq400 x
       grind)
    | exact superpose eq400 eq92382
    | exact resolve eq92382 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq92382
  have eq92405 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq92395
       have i₂ := eq2215 sF1
       grind)
    | exact superpose eq2215 eq92395
    | exact resolve eq92395 eq2215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215 eq92395
  have eq92409 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq48344 eq92405
    | exact resolve eq92405 eq48344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48344 eq92405
  have eq92413 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq47814 eq92409
    | exact resolve eq92409 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92409
  have eq92416 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq92413
       have i₂ := eq92163
       grind)
    | exact superpose eq92163 eq92413
    | exact resolve eq92413 eq92163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92163 eq92413
  have eq92423 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14626 eq92416
    | exact resolve eq92416 eq14626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14626 eq92416
  have eq92486 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq92423
       have r₂ := eq22455
       grind)
    | exact resolve eq92423 eq22455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22455 eq92423
  have eq92494 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48319 eq92486
    | exact resolve eq92486 eq48319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48319 eq92486
  have eq92498 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq47814 eq92494
    | exact resolve eq92494 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92494
  have eq93366 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq92498 eq92184
    | exact resolve eq92184 eq92498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92184
  have eq93381 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq92498 eq53
    | exact resolve eq53 eq92498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92498
  have eq93434 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq22246 eq93366
    | exact resolve eq93366 eq22246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93366
  have eq93452 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq47814 eq93434
    | exact resolve eq93434 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93434
  have eq93453 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq93452
  have eq93458 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq22246 eq93381
    | exact resolve eq93381 eq22246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22246 eq93381
  have eq93521 : x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq47814 eq93458
    | exact resolve eq93458 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93458
  have eq93522 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq93521
  have eq94294 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq93453 eq130
    | exact resolve eq130 eq93453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq93453
  have eq94354 : (τ (σ (M.op x y))) = (k y x) ∨ x = y := by
    first
    | exact superpose eq47814 eq94294
    | exact resolve eq94294 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94294
  have eq94364 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq94354
    | exact resolve eq94354 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq94354
  have eq94373 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq47814 eq94364
    | exact resolve eq94364 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94364
  have eq94415 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq93522 eq53
    | exact resolve eq53 eq93522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq93522
  have eq94612 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq94415 eq4598
    | exact resolve eq4598 eq94415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94415
  have eq94676 : (τ (σ y)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq47814 eq94612
    | exact resolve eq94612 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94612
  have eq94683 : (τ (σ y)) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq94676
       have i₂ := eq92084
       grind)
    | exact superpose eq92084 eq94676
    | exact resolve eq94676 eq92084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94676
  have eq94687 : y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq94683
    | exact resolve eq94683 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq94683
  have eq94862 : y = (k y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6841 x
       have i₂ := eq94687
       grind)
    | exact superpose eq94687 eq6841
    | exact resolve eq6841 eq94687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6841 eq94687
  have eq94906 : y = (M.op x y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq94862
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94862
    | exact resolve eq94862 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq94862
  have eq94932 : x = y ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq47814 eq94906
    | exact resolve eq94906 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94906
  have eq94933 : y = (k y x) ∨ x = y := by grind
  clear eq94932
  have eq95204 : x = y ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq94373
       have i₂ := eq94933
       grind)
    | exact superpose eq94933 eq94373
    | exact resolve eq94373 eq94933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94373 eq94933
  have eq95221 : x = y := by grind
  clear eq95204
  have eq95335 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq95221
       grind)
    | exact superpose eq95221 eq24
    | exact resolve eq24 eq95221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq95337 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54
       have i₂ := eq95221
       grind)
    | exact superpose eq95221 eq54
    | exact resolve eq54 eq95221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq95221
  have eq95624 : x = (M.op x x) := by
    first
    | exact superpose eq47814 eq95337
    | exact resolve eq95337 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95337
  have eq95626 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq95335
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95335
    | exact resolve eq95335 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95335
  have eq95732 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq48301 eq95626
    | exact resolve eq95626 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95626
  have eq95877 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq95732 eq26
    | exact resolve eq26 eq95732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq95732
  have eq96144 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq48301 eq95877
    | exact resolve eq95877 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95877
  have eq97165 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq96144 eq4598
    | exact resolve eq4598 eq96144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4598 eq96144
  have eq97222 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq47814 eq97165
    | exact resolve eq97165 eq47814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47814 eq97165
  have eq97233 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq97222
       have i₂ := eq92084
       grind)
    | exact superpose eq92084 eq97222
    | exact resolve eq97222 eq92084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92084 eq97222
  have eq97239 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq97233
       have i₂ := eq95624
       grind)
    | exact superpose eq95624 eq97233
    | exact resolve eq97233 eq95624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95624 eq97233
  have eq97250 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq97239 eq15
    | exact resolve eq15 eq97239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97239
  have eq97567 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97250
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq97250
    | exact resolve eq97250 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq97250
  have eq97690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48301 eq97567
    | exact resolve eq97567 eq48301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48301 eq97567
  have eq97766 : False := by grind
  exact eq97766

/-- `Equation2497`: `x = (y ◇ ((x ◇ x) ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2497 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2497 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2497.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq73
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq100
  have eq167 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq169 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq172 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq167
    | (have j0 := eq167 X0 X1
       grind)
    | exact resolve eq167 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq609 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq172 x y
       grind)
    | exact superpose eq172 eq16
    | (have j1 := eq172 x y
       grind)
    | exact resolve eq16 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq987 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq169
    | exact resolve eq169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq1045 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq987 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq987
    | (have j0 := eq987 X0 X1
       grind)
    | exact resolve eq987 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq4923 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq609
       have i₂ := eq1045 y x
       grind)
    | exact superpose eq1045 eq609
    | (have j1 := eq1045 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq609
       have r₂ := eq1045 y x
       grind)
    | (have r₁ := eq609
       have r₂ := eq1045 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq609
       have r₂ := eq1045 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq609 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq1045
  have eq4924 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq4923
  have eq4926 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4924
       grind)
    | exact superpose eq4924 eq16
    | exact resolve eq16 eq4924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4924
  have eq4927 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4926
       have r₂ := eq80 x
       grind)
    | exact resolve eq4926 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4926
  have eq4934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq4927
       grind)
    | exact superpose eq4927 eq103
    | exact resolve eq103 eq4927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4927
  have eq4952 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4934
       have r₂ := eq16
       grind)
    | exact resolve eq4934 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4934
  have eq4955 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4952
       grind)
    | exact superpose eq4952 eq10
    | exact resolve eq10 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq5004 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4955
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4955
    | exact resolve eq4955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4955
  have eq5007 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5004
       grind)
    | exact superpose eq5004 eq16
    | exact resolve eq16 eq5004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004
  have eq5008 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5007
       have r₂ := eq80 x
       grind)
    | exact resolve eq5007 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq5007
  have eq5018 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5008
       grind)
    | exact superpose eq5008 eq10
    | exact resolve eq10 eq5008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5008
  have eq5067 : y = (M.op x x) := by
    first
    | (have i₁ := eq5018
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5018
    | exact resolve eq5018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5018
  have eq5081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq5067
       grind)
    | exact superpose eq5067 eq103
    | exact resolve eq103 eq5067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq5067
  have eq5098 : False := by grind
  exact eq5098

/-- `Equation2497`: `x = (y ◇ ((x ◇ x) ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2497 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2497 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2497.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 X0) X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq51 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq51 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq52 (σ X0)
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq73 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq63
    | exact resolve eq63 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq87
  have eq128 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq146 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq128 X0 X1 X2
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq128
    | (have j0 := eq128 X0 X1 X2
       grind)
    | exact resolve eq128 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq152 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq146 X0 X1 X2
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq146
    | (have j0 := eq146 X0 X1 X2
       grind)
    | exact resolve eq146 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq146
  have eq1229 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k X3 (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq152 X0 X1 X2
       grind)
    | exact superpose eq152 eq13
    | (have j0 := eq13 X0 (k (σ X0) X1)
       have j1 := eq152 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq152 X0 X1 X2
       grind)
    | exact resolve eq13 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1241 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq152 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq1251 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k X3 (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1229 X0 X1 X2 X3
       have j1 := eq1241 X0 X1 X2
       grind)
    | (have r₁ := eq1229 X0 X1 X2 X3
       have r₂ := eq1241 X0 X1 X2
       grind)
    | exact resolve eq1229 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229 eq1241
  have eq80568 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1251 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq80571 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq80568 X0 X1 X2
       have j1 := eq12 (σ X2) (k (σ X0) X1)
       grind)
    | (have r₁ := eq80568 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq80568 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80568
  have eq80633 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80571 X0 X1 X2
       have i₂ := eq26 X0 X1 X2
       grind)
    | exact superpose eq26 eq80571
    | (have j0 := eq80571 X0 X1 X2
       grind)
    | exact resolve eq80571 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq80571
  have eq80634 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq80633 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80633
  have eq80948 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 (k X0 (τ X1))
       have i₂ := eq80634 X0 X1 (τ X2)
       grind)
    | exact superpose eq80634 eq17
    | exact resolve eq17 eq80634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq80634
  have eq81130 : ∀ X0 X1 X2 : G, (k X2 (σ (k X0 (τ X1)))) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80948 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq80948
    | exact resolve eq80948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80948
  have eq81313 : ∀ X0 X1 X2 : G, (k X2 (k (σ X0) X1)) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81130 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq81130
    | exact resolve eq81130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq81130
  have eq81505 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op (k X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81313 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81313
    | exact resolve eq81313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81313
  have eq82247 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81505 X0 X1 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq81505
    | exact resolve eq81505 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq82269 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (k X0 X1) X2)) = (M.op (M.op (k X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq81505 X1 X1 (k X0 X2)
       have i₂ := eq81505 X0 X1 X2
       grind)
    | exact superpose eq81505 eq81505
    | exact resolve eq81505 eq81505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81505
  have eq107253 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X2) = (k X2 (M.op (M.op (M.op X0 X0) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq82269 X1 (M.op X0 X0) X2 X3
       have i₂ := eq82247 X0 X1
       grind)
    | exact superpose eq82247 eq82269
    | exact resolve eq82269 eq82247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82247 eq82269
  have eq346696 : ∀ X0 X2 : G, (k X2 X0) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq107253 X0 (M.op (M.op X0 X0) (M.op X0 X0)) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq107253
    | exact resolve eq107253 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107253
  have eq347975 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq346696 (σ X0) (σ X1)
       grind)
    | exact superpose eq346696 eq15
    | exact resolve eq15 eq346696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348336 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq347975 X0 X1
       have i₂ := eq346696 X0 X1
       grind)
    | exact superpose eq346696 eq347975
    | exact resolve eq347975 eq346696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346696 eq347975
  have eq385050 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq348336 x y
       grind)
    | exact superpose eq348336 eq16
    | (have r₁ := eq16
       have r₂ := eq348336 x y
       grind)
    | exact resolve eq16 eq348336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348336
  have eq385336 : False := by grind
  exact eq385336

/-- `Equation2497`: `x = (y ◇ ((x ◇ x) ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation2497 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2497 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2497.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq448 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2860 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq448 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq448
    | exact resolve eq448 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq2900 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2860 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2860
    | (have j0 := eq2860 X0 X1
       grind)
    | exact resolve eq2860 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq2904 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2900 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq2900
    | (have j0 := eq2900 (τ X1) (τ X0)
       grind)
    | exact resolve eq2900 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2900
  have eq2993 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2904 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2904
    | (have j0 := eq2904 X0 X1
       grind)
    | exact resolve eq2904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq19567 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq2993 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq2993 X0 X1
       grind)
    | exact superpose eq2993 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq2993 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq2993 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq2993 X0 X1
       grind)
    | exact resolve eq13 eq2993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993
  have eq19568 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq19567 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19567
  have eq19569 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq19568 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19568
  have eq19578 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19569 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq19569
    | (have j0 := eq19569 X0 X1
       grind)
    | exact resolve eq19569 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19569
  have eq19621 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19578 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19578
    | exact resolve eq19578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19578
  have eq19690 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19621 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq19621
    | (have j0 := eq19621 X0 X1
       grind)
    | exact resolve eq19621 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19621
  have eq19743 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq19690 X0 X1
       grind)
    | exact superpose eq19690 eq10
    | (have j1 := eq19690 X0 X1
       grind)
    | exact resolve eq10 eq19690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19690
  have eq19839 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19743 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq19743
    | (have j0 := eq19743 X0 X1
       grind)
    | exact resolve eq19743 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq19743
  have eq19840 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq19839 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19839
  have eq19854 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19840 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19840
    | exact resolve eq19840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19898 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq19840 X1 X0
       grind)
    | exact superpose eq19840 eq19
    | (have j1 := eq19840 X1 X0
       grind)
    | exact resolve eq19 eq19840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq19840
  have eq20193 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq19854 (σ X0) (σ X1)
       grind)
    | exact superpose eq19854 eq15
    | (have j1 := eq19854 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq19854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19854
  have eq20306 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19898 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19898
    | exact resolve eq19898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19898
  have eq20447 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20306 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20306
    | (have j0 := eq20306 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq20306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20306
  have eq21823 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20193 x y
       grind)
    | exact superpose eq20193 eq16
    | (have j1 := eq20193 x y
       grind)
    | exact resolve eq16 eq20193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20193
  have eq21877 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21823
       have i₂ := eq20447 x y
       grind)
    | exact superpose eq20447 eq21823
    | (have j1 := eq20447 (σ x) (σ y)
       grind)
    | (have r₁ := eq21823
       have r₂ := eq20447 x y
       grind)
    | (have r₁ := eq21823
       have r₂ := eq20447 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq21823
       have r₂ := eq20447 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq21823 eq20447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20447 eq21823
  have eq21880 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq21877
  have eq21883 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21880
       grind)
    | exact superpose eq21880 eq16
    | exact resolve eq16 eq21880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21880
  have eq21884 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq21883
       have r₂ := eq22 x
       grind)
    | exact resolve eq21883 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21883
  have eq21885 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21884
       grind)
    | exact superpose eq21884 eq16
    | exact resolve eq16 eq21884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21886 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21884
       grind)
    | exact superpose eq21884 eq10
    | exact resolve eq10 eq21884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21884
  have eq22046 : x = y := by
    first
    | (have i₁ := eq21886
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21886
    | exact resolve eq21886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21886
  have eq22047 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq21885
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq21885
    | exact resolve eq21885 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21885
  have eq22048 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq22047
       have i₂ := eq22046
       grind)
    | exact superpose eq22046 eq22047
    | exact resolve eq22047 eq22046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22046 eq22047
  have eq22049 : False := by grind
  exact eq22049

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 X1) X0)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X0 X0) X0) X0)) = (k (M.op (M.op (M.op X0 X0) X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X0 X0) X0) X0) X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X0 X0) X0) X0) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X0 X0) X0) X0) X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X0) X0)) = (k (M.op (M.op (M.op X0 X0) X0) X0) X0) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq71 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq63
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq98 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2290 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq67
    | (have j1 := eq71 X0
       grind)
    | exact resolve eq67 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq2299 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2290 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq2326 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2299 (σ X0)
       grind)
    | exact superpose eq2299 eq15
    | exact resolve eq15 eq2299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2345 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2326 X0
       have i₂ := eq2299 X0
       grind)
    | exact superpose eq2299 eq2326
    | exact resolve eq2326 eq2299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299 eq2326
  have eq2448 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq16
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq5289 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq5319 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5289 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5289
    | (have j0 := eq5289 X0 X1
       grind)
    | exact resolve eq5289 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5289
  have eq37124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq2448
       have i₂ := eq5319 y x
       grind)
    | exact superpose eq5319 eq2448
    | (have j1 := eq5319 (σ y) (σ x)
       grind)
    | (have r₁ := eq2448
       have r₂ := eq5319 y x
       grind)
    | (have r₁ := eq2448
       have r₂ := eq5319 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2448
       have r₂ := eq5319 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2448 eq5319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37125 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq37124
  have eq37376 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37125
       grind)
    | exact superpose eq37125 eq16
    | exact resolve eq16 eq37125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37125
  have eq37377 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq37376
       have r₂ := eq2345 x
       grind)
    | exact resolve eq37376 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37376
  have eq37379 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq37377
       grind)
    | exact superpose eq37377 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq37377
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq37377
       grind)
    | exact resolve eq12 eq37377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37377
  have eq37382 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq37379
  have eq37383 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2448
       have i₂ := eq37382
       grind)
    | exact superpose eq37382 eq2448
    | exact resolve eq2448 eq37382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448 eq37382
  have eq37384 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq37383
  have eq37385 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq37384
  have eq37389 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq37385
       grind)
    | exact superpose eq37385 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq37385
       grind)
    | exact resolve eq12 eq37385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37385
  have eq37392 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq37389
  have eq37395 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37392
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq37392
    | exact resolve eq37392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37392
  have eq37408 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37395
       grind)
    | exact superpose eq37395 eq16
    | exact resolve eq16 eq37395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37395
  have eq37485 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq37408
       have i₂ := eq5319 y x
       grind)
    | exact superpose eq5319 eq37408
    | (have j1 := eq5319 y x
       grind)
    | (have r₁ := eq37408
       have r₂ := eq5319 y x
       grind)
    | (have r₁ := eq37408
       have r₂ := eq5319 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq37408
       have r₂ := eq5319 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq37408 eq5319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319
  have eq37486 : x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq37485
  have eq37491 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37486
       grind)
    | exact superpose eq37486 eq16
    | exact resolve eq16 eq37486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37486
  have eq37492 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq37491
       have r₂ := eq2345 x
       grind)
    | exact resolve eq37491 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37491
  have eq37494 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq37492
       grind)
    | exact superpose eq37492 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq37492
       grind)
    | exact resolve eq12 eq37492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37492
  have eq37497 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq37494
  have eq37498 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37408
       have i₂ := eq37497
       grind)
    | exact superpose eq37497 eq37408
    | exact resolve eq37408 eq37497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37408 eq37497
  have eq37502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq37498
  have eq37503 : (σ x) = (σ y) := by grind
  clear eq37502
  have eq37504 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq37503
       grind)
    | exact superpose eq37503 eq16
    | exact resolve eq16 eq37503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37505 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq37503
       grind)
    | exact superpose eq37503 eq10
    | exact resolve eq10 eq37503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37503
  have eq37600 : x = y := by
    first
    | (have i₁ := eq37505
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37505
    | exact resolve eq37505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37505
  have eq37601 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq37504
       have i₂ := eq2345 x
       grind)
    | exact superpose eq2345 eq37504
    | exact resolve eq37504 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345 eq37504
  have eq37620 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq37601
       have i₂ := eq37600
       grind)
    | exact superpose eq37600 eq37601
    | exact resolve eq37601 eq37600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37600 eq37601
  have eq37621 : False := by grind
  exact eq37621

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq23
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
  clear eq68
  have eq435 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq438 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3062 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq438
    | exact resolve eq438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq3119 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3062 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3062
    | (have j0 := eq3062 X0 X1
       grind)
    | exact resolve eq3062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062
  have eq3371 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (σ X1) X0) = (M.op X0 X0) ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq435 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq435 X0 X1
       grind)
    | exact superpose eq435 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq435 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq435 (σ X1) X1
       grind)
    | (have r₁ := eq12 (σ X1) X0
       have r₂ := eq435 X0 X1
       grind)
    | exact resolve eq12 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3374 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq435 (σ x) y
       grind)
    | exact superpose eq435 eq16
    | (have j1 := eq435 (σ y) x
       grind)
    | (have r₁ := eq16
       have r₂ := eq435 (M.op (σ x) (σ y)) (M.op x y)
       grind)
    | exact resolve eq16 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq3378 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3371 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3383 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3374
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq3374
    | exact resolve eq3374 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374
  have eq3394 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3383
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3383
    | exact resolve eq3383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383
  have eq3646 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3378 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3378
    | exact resolve eq3378 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3378
  have eq3745 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3646 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3646
    | (have j0 := eq3646 X0 X1
       grind)
    | exact resolve eq3646 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3646
  have eq3775 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3745 X1 X0
       grind)
    | exact superpose eq3745 eq11
    | (have j1 := eq3745 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq3745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3745
  have eq3892 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3775 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq3775
    | (have j0 := eq3775 X0 X1
       grind)
    | exact resolve eq3775 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq3934 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3892 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3892
    | (have j0 := eq3892 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq3892 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3983 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq3892 X0 (τ X1)
       grind)
    | exact superpose eq3892 eq18
    | (have j1 := eq3892 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq3892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3892
  have eq4092 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3934 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq3934
    | (have j0 := eq3934 X0 X1
       grind)
    | exact resolve eq3934 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3934
  have eq4253 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3983 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3983
    | exact resolve eq3983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3983
  have eq4318 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4253 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4253
    | (have j0 := eq4253 X0 X1
       grind)
    | exact resolve eq4253 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253
  have eq11395 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4092 y x
       grind)
    | exact superpose eq4092 eq16
    | (have j1 := eq4092 y x
       grind)
    | exact resolve eq16 eq4092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4092
  have eq11475 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11395
       have i₂ := eq3119 y x
       grind)
    | exact superpose eq3119 eq11395
    | (have j1 := eq3119 (σ (M.op x y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq11395
       have r₂ := eq3119 y x
       grind)
    | (have r₁ := eq11395
       have r₂ := eq3119 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11395
       have r₂ := eq3119 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11395 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11395
  have eq11476 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq11475
  have eq11609 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11476
       grind)
    | exact superpose eq11476 eq16
    | exact resolve eq16 eq11476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11476
  have eq11610 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11609
       have r₂ := eq79 x
       grind)
    | exact resolve eq11609 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11609
  have eq11611 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3394
       have i₂ := eq11610
       grind)
    | exact superpose eq11610 eq3394
    | (have r₁ := eq3394
       have r₂ := eq11610
       grind)
    | exact resolve eq3394 eq11610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11610
  have eq11616 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq11611
  have eq11617 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq11616
  have eq11618 : (σ x) = (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq11617
       have r₂ := eq3394
       grind)
    | exact resolve eq11617 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394 eq11617
  have eq11620 : y = (τ (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11618
       grind)
    | exact superpose eq11618 eq10
    | exact resolve eq10 eq11618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11618
  have eq11684 : x = y ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11620
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11620
    | exact resolve eq11620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11620
  have eq11686 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11684
       grind)
    | exact superpose eq11684 eq16
    | exact resolve eq16 eq11684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11684
  have eq11687 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq11686
       have r₂ := eq79 x
       grind)
    | exact resolve eq11686 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq11686
  have eq11702 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq11687
       grind)
    | exact superpose eq11687 eq11
    | exact resolve eq11 eq11687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11687
  have eq11797 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11702
       grind)
    | exact superpose eq11702 eq16
    | exact resolve eq16 eq11702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11702
  have eq11836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq11797
       have i₂ := eq4318 y x
       grind)
    | exact superpose eq4318 eq11797
    | (have j1 := eq4318 x y
       grind)
    | (have r₁ := eq11797
       have r₂ := eq4318 y x
       grind)
    | (have r₁ := eq11797
       have r₂ := eq4318 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11797
       have r₂ := eq4318 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11797 eq4318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4318
  have eq11837 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11797
       have i₂ := eq3119 y x
       grind)
    | exact superpose eq3119 eq11797
    | (have j1 := eq3119 x y
       grind)
    | (have r₁ := eq11797
       have r₂ := eq3119 y x
       grind)
    | (have r₁ := eq11797
       have r₂ := eq3119 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11797
       have r₂ := eq3119 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11797 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq11838 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq11837
  have eq11839 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq11836
  have eq11851 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq11797
       have i₂ := eq11839
       grind)
    | exact superpose eq11839 eq11797
    | exact resolve eq11797 eq11839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11839
  have eq11852 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq11851
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq11851
    | exact resolve eq11851 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq11851
  have eq11853 : (k y x) = (M.op x x) := by grind
  clear eq11852
  have eq11862 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11797
       have i₂ := eq11853
       grind)
    | exact superpose eq11853 eq11797
    | exact resolve eq11797 eq11853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11797 eq11853
  have eq11893 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq11862
       have i₂ := eq11838
       grind)
    | exact superpose eq11838 eq11862
    | exact resolve eq11862 eq11838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11838
  have eq11900 : x = y := by grind
  clear eq11893
  have eq11912 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11862
       have i₂ := eq11900
       grind)
    | exact superpose eq11900 eq11862
    | exact resolve eq11862 eq11900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11862 eq11900
  have eq11913 : False := by grind
  exact eq11913

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq336 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq349 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq336 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq350 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq349 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq355 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq350 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq350 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq363 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq355
    | (have j0 := eq355 X0 X1
       grind)
    | exact resolve eq355 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq364 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq369 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq364 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq364
    | exact resolve eq364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq364 x y
       grind)
    | exact superpose eq364 eq16
    | exact resolve eq16 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq451 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq369 X0 (τ X1)
       grind)
    | exact superpose eq369 eq17
    | exact resolve eq17 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq369
  have eq482 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq451
    | exact resolve eq451 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq497 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq482 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq482
    | exact resolve eq482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq536 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq380
       have i₂ := eq497 x y
       grind)
    | exact superpose eq497 eq380
    | exact resolve eq380 eq497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq497
  have eq537 : False := by grind
  exact eq537

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation2533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X1)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq25
  have eq56 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X1))) = X0 ∨ (M.op (M.op X1 (M.op (M.op X1 X0) X1)) (M.op X1 (M.op (M.op X1 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X1))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X1))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X1)) (M.op X1 (M.op (M.op X1 X0) X1))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq73 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq178 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq184 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq187 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq183 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq190 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq187
    | (have j0 := eq187 X0
       grind)
    | exact resolve eq187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq222 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X1)) X0) = (k X0 (M.op X1 (M.op (M.op X1 X0) X1))) ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X1))) = X0 := by
    intro X0 X1
    grind
  clear eq57
  have eq223 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X1))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq222
    | (have j0 := eq222 X0 X1
       grind)
    | exact resolve eq222 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq224 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq223 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq388 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (M.op (σ X0) (M.op (σ (k (k X0 X0) X0)) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq224 (σ (k X0 X0)) (σ X0)
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq224
    | (have j1 := eq190 X0
       grind)
    | exact resolve eq224 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq511 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq545 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq511
    | (have j0 := eq511 X0 X1
       grind)
    | exact resolve eq511 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq1083 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq545 (τ X1) (τ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq545
    | (have j0 := eq545 (τ X1) (τ X0)
       grind)
    | exact resolve eq545 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X1 X0) X2
       have i₂ := eq545 X0 X1
       grind)
    | exact superpose eq545 eq31
    | (have j1 := eq545 X0 X1
       grind)
    | exact resolve eq31 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1106 X0 X1 X2
       have i₂ := eq31 (M.op X0 X1) X2
       grind)
    | exact superpose eq31 eq1106
    | (have j0 := eq1106 X0 X1 X2
       grind)
    | exact resolve eq1106 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1106
  have eq1140 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1083 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1083
    | (have j0 := eq1083 X0 X1
       grind)
    | exact resolve eq1083 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq25163 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) (M.op X0 (M.op (σ (k (k (τ X0) (τ X0)) (τ X0))) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq388 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq388
    | exact resolve eq388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq25233 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) (M.op X0 (M.op (k (σ (k (τ X0) (τ X0))) X0) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25163 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq25163
    | (have j0 := eq25163 X0
       grind)
    | exact resolve eq25163 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25163
  have eq25270 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) (M.op X0 (M.op (k (k (σ (τ X0)) X0) X0) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25233 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq25233
    | (have j0 := eq25233 X0
       grind)
    | exact resolve eq25233 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25233
  have eq25301 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (M.op X0 (M.op (k (k X0 X0) X0) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25270 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25270
    | (have j0 := eq25270 X0
       grind)
    | exact resolve eq25270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25270
  have eq32039 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (M.op X2 X1) X0) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1127 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1127
    | (have j0 := eq1127 X2 X1 X2
       grind)
    | exact resolve eq1127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq32397 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op (k (k X0 X0) X0) X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25301 X0
       have i₂ := eq32039 (M.op X0 (M.op (k (k X0 X0) X0) X0)) X0 X0
       grind)
    | exact superpose eq32039 eq25301
    | (have j0 := eq25301 X0
       have j1 := eq32039 X0 X0 X0
       grind)
    | exact resolve eq25301 eq32039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25301
  have eq32535 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op (k (k X0 X0) X0) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq32397 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32397
  have eq33639 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op (k (M.op X0 X0) X0) X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32535 X0
       have i₂ := eq32039 X0 X0 X0
       grind)
    | exact superpose eq32039 eq32535
    | (have j0 := eq32535 X0
       have j1 := eq32039 X0 X0 X0
       grind)
    | exact resolve eq32535 eq32039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32039 eq32535
  have eq33667 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op (k (M.op X0 X0) X0) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq33639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33639
  have eq33683 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op (M.op X0 (M.op X0 X0)) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq33667
  have eq33700 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq33683 X0
       have i₂ := eq224 (M.op X0 X0) X0
       grind)
    | exact superpose eq224 eq33683
    | (have j0 := eq33683 X0
       grind)
    | exact resolve eq33683 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq33683
  have eq33935 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq33700
  have eq33996 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq33935 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33935
  have eq34130 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33996 (σ X0)
       grind)
    | exact superpose eq33996 eq15
    | exact resolve eq15 eq33996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34140 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq33996 (τ X0)
       grind)
    | exact superpose eq33996 eq35
    | exact resolve eq35 eq33996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34213 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34140 X0
       have i₂ := eq33996 X0
       grind)
    | exact superpose eq33996 eq34140
    | exact resolve eq34140 eq33996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34140
  have eq34221 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34130 X0
       have i₂ := eq33996 X0
       grind)
    | exact superpose eq33996 eq34130
    | exact resolve eq34130 eq33996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33996 eq34130
  have eq35726 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq35825 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq35726 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq35726
    | exact resolve eq35726 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35726
  have eq35915 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq35825
  have eq508406 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq1140 X0 X1
       grind)
    | exact superpose eq1140 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq1140 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq1140 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq1140 X0 X0
       grind)
    | exact resolve eq13 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq508429 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq508406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508406
  have eq508430 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq508429 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508429
  have eq508476 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq508430 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq508430
    | (have j0 := eq508430 X0 X1
       grind)
    | exact resolve eq508430 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq508430
  have eq508714 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq508476 X0 X1
       have i₂ := eq34213 X1
       grind)
    | exact superpose eq34213 eq508476
    | (have j0 := eq508476 X0 X1
       grind)
    | exact resolve eq508476 eq34213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34213 eq508476
  have eq509771 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq508714 X0 X1
       grind)
    | exact superpose eq508714 eq11
    | (have j1 := eq508714 X0 X1
       grind)
    | exact resolve eq11 eq508714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508714
  have eq510152 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq509771 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq509771
    | (have j0 := eq509771 X0 X1
       grind)
    | exact resolve eq509771 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509771
  have eq516239 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq510152 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq510152
    | (have j0 := eq510152 X1 (σ X0)
       grind)
    | exact resolve eq510152 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510152
  have eq517150 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq516239 X0 X1
       have i₂ := eq34221 X0
       grind)
    | exact superpose eq34221 eq516239
    | (have j0 := eq516239 X0 X1
       grind)
    | exact resolve eq516239 eq34221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516239
  have eq517361 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq517150 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq517150
    | (have j0 := eq517150 X0 X1
       grind)
    | exact resolve eq517150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517150
  have eq526967 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq517361 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq517361
    | (have j0 := eq517361 X1 (σ X0)
       grind)
    | exact resolve eq517361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517361
  have eq527783 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq526967 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq526967
    | (have j0 := eq526967 X0 X1
       grind)
    | exact resolve eq526967 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526967
  have eq527942 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq527783 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq527783
    | (have j0 := eq527783 X0 X1
       grind)
    | exact resolve eq527783 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527783
  have eq530233 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq178
       have i₂ := eq527942 y x
       grind)
    | exact superpose eq527942 eq178
    | (have j1 := eq527942 y x
       grind)
    | (have r₁ := eq178
       have r₂ := eq527942 y x
       grind)
    | exact resolve eq178 eq527942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq527942
  have eq530606 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x x) := by grind
  clear eq530233
  have eq530875 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq184 x y
       grind)
    | (have r₁ := eq530606
       have r₂ := eq184 x y
       grind)
    | exact resolve eq530606 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq530606
  have eq531131 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq530875
       have i₂ := eq34221 x
       grind)
    | exact superpose eq34221 eq530875
    | exact resolve eq530875 eq34221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530875
  have eq532708 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq531131
       grind)
    | exact superpose eq531131 eq16
    | exact resolve eq16 eq531131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532726 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq531131
       grind)
    | exact superpose eq531131 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq531131
       grind)
    | exact resolve eq13 eq531131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531131
  have eq532752 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq532726
  have eq532755 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq532752
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq532752
    | exact resolve eq532752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532752
  have eq532773 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq532755
       have i₂ := eq34221 x
       grind)
    | exact superpose eq34221 eq532755
    | exact resolve eq532755 eq34221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34221 eq532755
  have eq532774 : y = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq532773
  have eq534406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq35915 x
       have i₂ := eq532774
       grind)
    | exact superpose eq532774 eq35915
    | exact resolve eq35915 eq532774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532774
  have eq534476 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq534406
       have r₂ := eq16
       grind)
    | exact resolve eq534406 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534406
  have eq534581 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq545 x y
       have i₂ := eq534476
       grind)
    | exact superpose eq534476 eq545
    | (have j0 := eq545 x y
       grind)
    | exact resolve eq545 eq534476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq534476
  have eq535241 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq534581
       have r₂ := eq532708
       grind)
    | exact resolve eq534581 eq532708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534581
  have eq541693 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq532708
       have i₂ := eq535241
       grind)
    | exact superpose eq535241 eq532708
    | exact resolve eq532708 eq535241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532708 eq535241
  have eq541728 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq541693
  have eq541729 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq541728
  have eq541883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq35915 x
       have i₂ := eq541729
       grind)
    | exact superpose eq541729 eq35915
    | exact resolve eq35915 eq541729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541729
  have eq541953 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq541883
       have r₂ := eq16
       grind)
    | exact resolve eq541883 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541883
  have eq543634 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq541953
       grind)
    | exact superpose eq541953 eq10
    | exact resolve eq10 eq541953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541953
  have eq544276 : y = (M.op x x) := by
    first
    | (have i₁ := eq543634
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq543634
    | exact resolve eq543634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543634
  have eq544837 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35915 x
       have i₂ := eq544276
       grind)
    | exact superpose eq544276 eq35915
    | exact resolve eq35915 eq544276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35915 eq544276
  have eq544908 : False := by grind
  exact eq544908
