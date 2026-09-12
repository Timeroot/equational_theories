import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_x_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq57 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq59 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq67 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq67
    | (have j0 := eq67 y x
       grind)
    | exact resolve eq67 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op X2 X1) (M.op X0 X0)) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq67
    | (have j0 := eq67 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq67 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq91 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq98
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq124 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq132 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
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
  have eq149 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq57 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (M.op (σ x) (σ y)) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq216 eq56
    | exact resolve eq56 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
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
  have eq294 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq372 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq67
    | (have j0 := eq67 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact resolve eq67 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X0)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq56
    | exact resolve eq56 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq58 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq59 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq58 X0 x x X3
       grind)
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq58 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq58 eq57
    | exact resolve eq57 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq58 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq58 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq436 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq435 X0 X1 X2 X3
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq435
    | exact resolve eq435 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq437 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq434
    | exact resolve eq434 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq438 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 X1
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq433
    | exact resolve eq433 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq491 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq667 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq67
    | (have j0 := eq67 (σ X0) (σ X1)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq67 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq67 (σ X0) (σ X0)
       have r₂ := eq89 X0 X0
       grind)
    | exact resolve eq67 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 : G, (σ X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (σ X0)
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq57
    | (have j1 := eq89 X0 X0
       grind)
    | exact resolve eq57 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq683 : ∀ X0 : G, (σ X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq687 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq667 X0 X1
       have j1 := eq67 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq667 X0 X1
       have r₂ := eq67 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq667 X0 X0
       have r₂ := eq67 (σ X0) (σ X0)
       grind)
    | exact resolve eq667 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq667
  have eq697 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq687 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq687 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq687 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq705 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq697
    | (have j0 := eq697 X0 X1
       grind)
    | exact resolve eq697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq886
    | exact resolve eq886 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq890 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq887
       have r₂ := eq27
       grind)
    | exact resolve eq887 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq892 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq890
    | exact resolve eq890 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq894 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq892
    | exact resolve eq892 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq897 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq894 eq51
    | (have r₁ := eq51
       have r₂ := eq894
       grind)
    | exact resolve eq51 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq894
  have eq907 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq897
  have eq909 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq907
       have r₂ := eq82
       grind)
    | exact resolve eq907 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq907
  have eq987 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq909 eq80
    | exact resolve eq80 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq909
  have eq994 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq987
    | exact resolve eq987 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq997 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq994
       have r₂ := eq81
       grind)
    | exact resolve eq994 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq994
  have eq999 : y = (k y x) := by
    first
    | (have r₁ := eq997
       have r₂ := eq50
       grind)
    | exact resolve eq997 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq997
  have eq1001 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq999
       grind)
    | exact superpose eq999 eq73
    | exact resolve eq73 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1002 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq999
       grind)
    | exact superpose eq999 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1003 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1002
  have eq1005 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1003
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1003
    | exact resolve eq1003 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1006 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1001
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1001
    | exact resolve eq1001 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1008 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1005
    | exact resolve eq1005 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1014 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1006 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1014
  have eq1017 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1015
    | exact resolve eq1015 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1020 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1017
    | exact resolve eq1017 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1029 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq216 eq218
    | exact resolve eq218 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq218 eq57
    | exact resolve eq57 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq216 eq1062
    | exact resolve eq1062 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1111 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1008 eq20
    | exact resolve eq20 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : ∀ X0 : G, (M.op y (M.op y (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1008 eq56
    | exact resolve eq56 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1008 eq124
    | exact resolve eq124 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : (σ (k y y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1008 eq132
    | exact resolve eq132 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1120 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1008 eq133
    | exact resolve eq133 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1008
  have eq1134 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1120
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq1120
    | exact resolve eq1120 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1135 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1119
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq1119
    | exact resolve eq1119 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1137 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1117 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq1117
    | exact resolve eq1117 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1117
  have eq1140 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1111
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1111
    | exact resolve eq1111 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1142 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1020 eq27
    | exact resolve eq27 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1144 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op X0 X0))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1020 eq57
    | exact resolve eq57 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1155 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1140 eq26
    | exact resolve eq26 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1140 eq1142
    | (have r₁ := eq1142
       have r₂ := eq1140
       grind)
    | exact resolve eq1142 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1231 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1230
  have eq1303 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1155 eq59
    | exact resolve eq59 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1309 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq216 eq1303
    | exact resolve eq1303 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1314 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq218 eq398
    | exact resolve eq398 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1327 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 X3)) (M.op X3 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq398 X2 X3 (M.op X1 X0)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq398
    | exact resolve eq398 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1364 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op X0 X0))
       have i₂ := eq398 X0 X0 X0
       grind)
    | exact superpose eq398 eq56
    | exact resolve eq56 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1365 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 (M.op X0 X0))
       have i₂ := eq398 X0 X0 X0
       grind)
    | exact superpose eq398 eq57
    | exact resolve eq57 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1376 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq428 (M.op x (M.op x x)) x
       have i₂ := eq398 x x x
       grind)
    | exact superpose eq398 eq428
    | exact resolve eq428 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1398 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq216 eq1314
    | exact resolve eq1314 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1446 : (k y y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1135 eq88
    | exact resolve eq88 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1452 : (k y y) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149 eq1446
    | exact resolve eq1446 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq1446
  have eq2607 : (σ y) ≠ (σ (k y y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1452 eq705
    | (have j0 := eq705 y y
       grind)
    | exact resolve eq705 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq2684 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2607
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq2607
    | exact resolve eq2607 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607
  have eq2718 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2684
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2684
    | exact resolve eq2684 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq2731 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2718
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq2718
    | exact resolve eq2718 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718
  have eq2743 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2731
    | exact resolve eq2731 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731
  have eq3807 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq378 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq378 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq378 eq378
    | exact resolve eq378 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3816 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq377 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       have i₂ := eq378 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq378 eq377
    | exact resolve eq377 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4444 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq437 X0 X1
       grind)
    | exact superpose eq437 eq438
    | exact resolve eq438 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq4548 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4444 y (M.op y (M.op X0 X0))
       have i₂ := eq1114 X0
       grind)
    | exact superpose eq1114 eq4444
    | exact resolve eq4444 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4557 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq4444
    | (have j0 := eq4444 (σ x) (σ y)
       grind)
    | exact resolve eq4444 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4444
  have eq4614 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq216 eq4557
    | exact resolve eq4557 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq4654 : ∀ X0 X1 : G, (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) = (k (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq491 (M.op X0 X1) (M.op X1 (M.op X0 X1))
       have i₂ := eq437 X0 X1
       grind)
    | exact superpose eq437 eq491
    | exact resolve eq491 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq4772 : ∀ X0 X1 : G, (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (k (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4654 X0 X0
       have i₂ := eq59 X0 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq4654
    | exact resolve eq4654 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654
  have eq4787 : ∀ X0 X1 : G, (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op y (M.op (M.op x y) (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4772 X0 X1
       have i₂ := eq437 X0 X1
       grind)
    | exact superpose eq437 eq4772
    | exact resolve eq4772 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4772
  have eq4790 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4787 X0 X1
       have i₂ := eq59 y (M.op sF0 (M.op X0 X1))
       grind)
    | exact superpose eq59 eq4787
    | exact resolve eq4787 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4787
  have eq5288 : ∀ X0 X1 X4 X5 X6 X7 : G, (M.op X0 X1) = (M.op (M.op (M.op X5 X6) (M.op X7 X7)) (M.op X7 (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1)))) := by
    intro X0 X1 X4 X5 X6 X7
    first
    | (have i₁ := eq418 (M.op X4 (M.op X0 (M.op X1 X0))) (M.op (M.op x x) (M.op X4 X4)) x x X4
       have i₂ := eq418 X0 X1 x x X4
       grind)
    | exact superpose eq418 eq418
    | exact resolve eq418 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5343 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X3 (M.op X0 X0)))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq418 X0 X0 X1 X2 (M.op X3 (M.op X0 X0))
       have i₂ := eq398 X3 X0 X0
       grind)
    | exact superpose eq398 eq418
    | exact resolve eq418 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5432 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op X0 X0) (M.op X3 (M.op X0 X0)))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5343 X0 X1 X2 X3
       have i₂ := eq59 X3 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq5343
    | exact resolve eq5343 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq5343
  have eq5657 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq436 X0 X1 X2 X3
       have i₂ := eq437 X0 X1
       grind)
    | exact superpose eq437 eq436
    | exact resolve eq436 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq437
  have eq5706 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X1 X2))) = (M.op (M.op X3 (M.op X0 X0)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5657 X1 X2 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3))
       have i₂ := eq398 x X3 X0
       grind)
    | exact superpose eq398 eq5657
    | exact resolve eq5657 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5803 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5657 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq398 x X1 X0
       grind)
    | exact superpose eq398 eq5657
    | exact resolve eq5657 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq5813 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5657 (M.op X1 (M.op X2 X3)) (M.op X0 X0) X3 X2
       have i₂ := eq14 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq14 eq5657
    | exact resolve eq5657 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5815 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op X3 X4)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5657 (M.op X2 (M.op X3 X4)) (M.op X0 X1) X4 X3
       have i₂ := eq5657 X0 X1 (M.op X3 X4) X2
       grind)
    | exact superpose eq5657 eq5657
    | exact resolve eq5657 eq5657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5853 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X3))) = (M.op X3 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq378 (M.op X1 (M.op X2 X3)) X0 X3 X2
       have i₂ := eq5657 X0 (M.op X1 (M.op X2 X3)) (M.op X2 X3) X1
       grind)
    | exact superpose eq5657 eq378
    | exact resolve eq378 eq5657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq5657
  have eq6712 : ∀ X0 : G, (σ X0) ≠ (M.op (M.op (M.op (σ x) (σ y)) (σ (k X0 X0))) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq683 eq373
    | (have j1 := eq683 X0
       grind)
    | exact resolve eq373 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq683
  have eq6731 : ∀ X0 : G, (σ X0) ≠ (M.op (M.op (M.op (σ x) (σ y)) (σ (k X0 X0))) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq6712 X0
       have j1 := eq13 (σ X0) (M.op (M.op (σ x) (σ y)) (σ (k X0 X0)))
       grind)
    | (have r₁ := eq6712 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | exact resolve eq6712 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712
  have eq6753 : ∀ X0 : G, (σ X0) ≠ (M.op (M.op (M.op (σ x) (σ y)) (σ (k X0 X0))) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6731 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq6731
    | (have j0 := eq6731 X0
       grind)
    | exact resolve eq6731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6731
  have eq7611 : (σ (k y (k y x))) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq91 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq91
    | exact resolve eq91 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq7658 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq91 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq7669 : (σ (k y (k y x))) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq1006 eq7611
    | exact resolve eq7611 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7611
  have eq7678 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq7669
       have i₂ := eq999
       grind)
    | exact superpose eq999 eq7669
    | exact resolve eq7669 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq7669
  have eq7683 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq7678
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq7678
    | exact resolve eq7678 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7678
  have eq7684 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq1006 eq7683
    | exact resolve eq7683 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7683
  have eq7685 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1006 eq7684
    | exact resolve eq7684 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq7684
  have eq7686 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq7685
  have eq7696 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq7686 eq88
    | exact resolve eq88 eq7686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8026 : ∀ X0 : G, (σ X0) ≠ (σ (k (M.op x y) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq8672 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq268
    | exact resolve eq268 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq8740 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8672 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq8672
    | (have j0 := eq8672 X0 X1
       grind)
    | exact resolve eq8672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8672
  have eq9807 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (M.op x y)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (τ X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq124 eq677
    | (have j0 := eq677 (τ X0) (M.op x y)
       grind)
    | exact resolve eq677 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq677
  have eq9847 : ∀ X0 : G, (k (σ (M.op x y)) X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (τ X0)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9807 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9807
    | (have j0 := eq9807 X0
       grind)
    | exact resolve eq9807 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9807
  have eq9914 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) X0) ≠ X0 ∨ (σ (M.op x y)) = (M.op (σ (τ X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq9847
    | (have j0 := eq9847 X0
       grind)
    | exact resolve eq9847 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9847
  have eq9977 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ (k (σ (M.op x y)) X0) ≠ X0 ∨ (σ (M.op x y)) = (M.op (σ (τ X0)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9914 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9914
    | (have j0 := eq9914 X0
       grind)
    | exact resolve eq9914 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9914
  have eq10024 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (τ X0)) (σ (M.op x y))) ∨ (M.op X0 (σ (M.op x y))) = X0 ∨ (k (σ (M.op x y)) X0) ≠ X0 := by
    intro X0
    first
    | exact superpose eq20 eq9977
    | (have j0 := eq9977 X0
       grind)
    | exact resolve eq9977 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9977
  have eq10060 : ∀ X0 : G, (k (σ (M.op x y)) X0) ≠ X0 ∨ (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq10024 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10024
    | (have j0 := eq10024 X0
       grind)
    | exact resolve eq10024 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10024
  have eq11672 : (σ y) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1134 eq2743
    | exact resolve eq2743 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743
  have eq11679 : (σ y) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq11672
  have eq14026 : (σ y) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11679
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq11679
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11679 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11679
  have eq14027 : (σ y) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq14026
  have eq19001 : (M.op y (M.op (M.op x y) (M.op (σ y) (M.op (σ x) (σ y))))) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1083 eq4548
    | exact resolve eq4548 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4548
  have eq19054 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq230 eq19001
    | exact resolve eq19001 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq19001
  have eq19061 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1309 eq19054
    | exact resolve eq19054 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309 eq19054
  have eq19102 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by grind
  clear eq19061
  have eq19188 : (σ x) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x y)) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1231 eq19102
    | exact resolve eq19102 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19230 : (σ x) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x y)) (σ x)))) ∨ x = (M.op x y) := by grind
  clear eq19188
  have eq20426 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1140 eq1365
    | exact resolve eq1365 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq21921 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq20426 X0
       grind)
    | exact superpose eq20426 eq372
    | exact resolve eq372 eq20426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22023 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq20426 eq418
    | exact resolve eq418 eq20426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22091 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22023 x x x
       have i₂ := eq418 sF1 sF1 x x x
       grind)
    | exact superpose eq418 eq22023
    | exact resolve eq22023 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq22023
  have eq22143 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1231 eq22091
    | exact resolve eq22091 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22091
  have eq22189 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq22143
  have eq22194 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22189 eq1155
    | exact resolve eq1155 eq22189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq22189
  have eq22233 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq22194
  have eq22237 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22233 eq14027
    | exact resolve eq14027 eq22233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14027 eq22233
  have eq22331 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22237
  have eq22343 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22331
       have r₂ := eq27
       grind)
    | exact resolve eq22331 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22331
  have eq22346 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1231 eq22343
    | exact resolve eq22343 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22352 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq22346
  have eq24064 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x y)) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1231 eq21921
    | exact resolve eq21921 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21921
  have eq24182 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x y)) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24064
  have eq24551 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq24182
    | (have j0 := eq24182 (σ y)
       grind)
    | exact resolve eq24182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24182
  have eq24674 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1231 eq24551
    | exact resolve eq24551 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq24681 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24551 eq19102
    | exact resolve eq19102 eq24551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19102
  have eq24724 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24681
  have eq24730 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq24674
  have eq24742 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24724 eq7696
    | exact resolve eq7696 eq24724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24724
  have eq24852 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24742
       have r₂ := eq22343
       grind)
    | exact resolve eq24742 eq22343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24742
  have eq25558 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24730 eq19230
    | exact resolve eq19230 eq24730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19230 eq24730
  have eq25599 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25558
  have eq25617 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25599 eq7696
    | exact resolve eq7696 eq25599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7696 eq25599
  have eq25724 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25617
       have r₂ := eq22352
       grind)
    | exact resolve eq25617 eq22352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22352 eq25617
  have eq25726 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq25724
    | exact resolve eq25724 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25724
  have eq25786 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq25726
       grind)
    | exact superpose eq25726 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq25726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25726
  have eq25798 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq25786
  have eq48253 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1083 eq1029
    | exact resolve eq1029 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq48254 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq4614 eq48253
    | exact resolve eq48253 eq4614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48253
  have eq82155 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1083 eq1398
    | exact resolve eq1398 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq1398
  have eq82156 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq4614 eq82155
    | exact resolve eq82155 eq4614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4614 eq82155
  have eq124810 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op X0 X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24551 eq5813
    | exact resolve eq5813 eq24551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24551
  have eq125082 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ y) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5803 eq124810
    | exact resolve eq124810 eq5803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803 eq124810
  have eq135801 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq125082 eq82156
    | exact resolve eq82156 eq125082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82156 eq125082
  have eq136170 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq48254 eq135801
    | exact resolve eq135801 eq48254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48254 eq135801
  have eq258542 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X3 (M.op X0 X0)))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5432 X0 X1 X2 X3
       have i₂ := eq3807 X3 X0 X0
       grind)
    | exact superpose eq3807 eq5432
    | exact resolve eq5432 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5432
  have eq276231 : (σ y) ≠ (M.op (M.op (M.op (σ x) (σ y)) (σ (τ (M.op (σ x) (σ y))))) (σ y)) ∨ (σ y) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6753 y
       have i₂ := eq24852
       grind)
    | exact superpose eq24852 eq6753
    | exact resolve eq6753 eq24852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753 eq24852
  have eq276510 : (σ y) ≠ (M.op (M.op (M.op (σ x) (σ y)) (σ (τ (M.op (σ x) (σ y))))) (σ y)) ∨ (σ y) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq276231
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq276231
    | exact resolve eq276231 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276231
  have eq276541 : (σ y) ≠ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq276510
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq276510
    | exact resolve eq276510 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276510
  have eq276564 : (σ y) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq216 eq276541
    | exact resolve eq276541 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq276541
  have eq276585 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq276564
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq276564
    | exact resolve eq276564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276564
  have eq276599 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq276585
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq276585
    | exact resolve eq276585 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276585
  have eq276609 : (σ y) ≠ (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq276599
       have r₂ := eq22343
       grind)
    | exact resolve eq276599 eq22343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22343 eq276599
  have eq276625 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq136170 eq276609
    | exact resolve eq276609 eq136170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136170 eq276609
  have eq276630 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq276625
  have eq276643 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1140 eq276630
    | exact resolve eq276630 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq276650 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq276643
  have eq279786 : (σ (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1134 eq8740
    | (have j0 := eq8740 (σ y) (σ y)
       grind)
    | exact resolve eq8740 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq8740
  have eq280394 : (σ (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq279786
  have eq280521 : (σ (k (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq280394
       have r₂ := eq276630
       grind)
    | exact resolve eq280394 eq276630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280394
  have eq282200 : (k (σ (M.op x y)) (σ (M.op x y))) = (τ (σ (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq280521 eq16
    | exact resolve eq16 eq280521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280521
  have eq282429 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq282200
       have i₂ := eq16 (M.op sF3 sF3)
       grind)
    | exact superpose eq16 eq282200
    | exact resolve eq282200 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282200
  have eq282478 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq282429 eq10060
    | (have j0 := eq10060 (σ (M.op x y))
       grind)
    | exact resolve eq10060 eq282429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10060
  have eq282490 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq282429 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq282429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282429
  have eq282505 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq282490
  have eq282507 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq282478
  have eq282536 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq282505
       have r₂ := eq276650
       grind)
    | exact resolve eq282505 eq276650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282505
  have eq282541 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq282507
       have r₂ := eq276650
       grind)
    | exact resolve eq282507 eq276650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276650 eq282507
  have eq284412 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 X0)) (M.op (σ (M.op x y)) (σ (M.op x y)))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq282536 eq5813
    | exact resolve eq5813 eq282536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282536
  have eq284635 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5813 eq284412
    | exact resolve eq284412 eq5813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5813 eq284412
  have eq287318 : (σ y) ≠ (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq284635 eq276630
    | exact resolve eq276630 eq284635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276630
  have eq287322 : (σ (M.op x y)) ≠ (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq284635 eq282541
    | exact resolve eq282541 eq284635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282541 eq284635
  have eq287373 : (σ (M.op x y)) ≠ (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq287322
  have eq287377 : (σ y) ≠ (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq287318
  have eq304838 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1452 eq8026
    | (have j0 := eq8026 y
       grind)
    | exact resolve eq8026 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq8026
  have eq304919 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq304838
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq304838
    | exact resolve eq304838 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq304838
  have eq304964 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq304919
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq304919
    | exact resolve eq304919 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304919
  have eq305003 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq304964
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq304964
    | exact resolve eq304964 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304964
  have eq305009 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq305003
       have r₂ := eq287377
       grind)
    | exact resolve eq305003 eq287377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287377 eq305003
  have eq305013 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) ≠ (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq305009
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq305009
    | exact resolve eq305009 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305009
  have eq305015 : (σ y) ≠ (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq305013
       have r₂ := eq287373
       grind)
    | exact resolve eq305013 eq287373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287373 eq305013
  have eq305027 : (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1137 eq305015
    | exact resolve eq305015 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305015
  have eq305030 : (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq305027
  have eq334948 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq20426 eq3816
    | exact resolve eq3816 eq20426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816 eq20426
  have eq335693 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq334948 X0 X1
       have i₂ := eq1376 X0 sF4
       grind)
    | exact superpose eq1376 eq334948
    | exact resolve eq334948 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376 eq334948
  have eq335876 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq377 eq335693
    | exact resolve eq335693 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq335693
  have eq369186 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1144 eq5853
    | exact resolve eq5853 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5853
  have eq369751 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op X0 (M.op y y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq369186 eq1327
    | exact resolve eq1327 eq369186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327 eq369186
  have eq370023 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq369751 x
       have i₂ := eq428 y x
       grind)
    | exact superpose eq428 eq369751
    | exact resolve eq369751 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369751
  have eq655924 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op y (M.op (M.op x y) (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1)))) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq5288 X0 X1 X4 x x x
       have i₂ := eq5706 x (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1) (M.op x x)
       grind)
    | exact superpose eq5706 eq5288
    | exact resolve eq5288 eq5706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5288 eq5706
  have eq655925 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq5815 eq655924
    | exact resolve eq655924 eq5815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5815 eq655924
  have eq1290519 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k (M.op (M.op X0 X1) (M.op y (M.op (M.op x y) (M.op X0 X1)))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4790 X0 X1
       have i₂ := eq3807 y sF0 (M.op X0 X1)
       grind)
    | exact superpose eq3807 eq4790
    | exact resolve eq4790 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3807 eq4790
  have eq1290520 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq655925 eq1290519
    | exact resolve eq1290519 eq655925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290519
  have eq1292052 : ∀ X0 : G, (k X0 (M.op (M.op y (M.op X0 X0)) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1290520 y (M.op y (M.op X0 X0))
       have i₂ := eq1114 X0
       grind)
    | exact superpose eq1114 eq1290520
    | exact resolve eq1290520 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1292421 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) (M.op X0 X0)) X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1144 eq1290520
    | exact resolve eq1290520 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1292828 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1292421 X0
       have i₂ := eq428 X0 sF3
       grind)
    | exact superpose eq428 eq1292421
    | exact resolve eq1292421 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292421
  have eq1292883 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1292052 X0
       have i₂ := eq428 X0 y
       grind)
    | exact superpose eq428 eq1292052
    | exact resolve eq1292052 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292052
  have eq1293331 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1292883 (τ X0)
       grind)
    | exact superpose eq1292883 eq34
    | exact resolve eq34 eq1292883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1292883
  have eq1293709 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1293331 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1293331
    | exact resolve eq1293331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293331
  have eq1294196 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq349 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1292828 (σ X0)
       grind)
    | exact superpose eq1292828 eq349
    | exact resolve eq349 eq1292828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq1292828
  have eq1294549 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1294196 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1294196
    | exact resolve eq1294196 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294196
  have eq1827655 : (σ y) = (k (σ (M.op x y)) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1137 (σ (M.op (τ sF3) (τ sF3)))
       have i₂ := eq1293709 sF3
       grind)
    | exact superpose eq1293709 eq1137
    | exact resolve eq1137 eq1293709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq1293709
  have eq1827922 : (σ y) = (k (σ (M.op x y)) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ x = (M.op x y) := by grind
  clear eq1827655
  have eq1828240 : (σ y) = (σ (k (M.op x y) (M.op (τ (σ y)) (τ (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq1827922
    | exact resolve eq1827922 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1827922
  have eq1828567 : (σ y) = (σ (k (M.op x y) (M.op y y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1828240
    | exact resolve eq1828240 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1828240
  have eq1932983 : y = (τ (k (σ y) (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq294 (M.op (σ y) (σ y))
       have i₂ := eq1294549 y
       grind)
    | exact superpose eq1294549 eq294
    | exact resolve eq294 eq1294549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq1294549
  have eq1933833 : y = (τ (k (σ y) (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1932983
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1932983
    | exact resolve eq1932983 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932983
  have eq2036307 : (σ y) = (σ (k (M.op x y) y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1828567
       have i₂ := eq25798
       grind)
    | exact superpose eq25798 eq1828567
    | exact resolve eq1828567 eq25798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25798 eq1828567
  have eq2037072 : (σ y) = (σ (k (M.op x y) y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq2036307
  have eq2037279 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq132 eq2037072
    | exact resolve eq2037072 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq2037072
  have eq2037332 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2037279
       have r₂ := eq305030
       grind)
    | exact resolve eq2037279 eq305030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305030 eq2037279
  have eq2039812 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq335876 y y
       have i₂ := eq2037332
       grind)
    | exact superpose eq2037332 eq335876
    | exact resolve eq335876 eq2037332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335876 eq2037332
  have eq2039891 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2039812
  have eq2039961 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2039891
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2039891
    | exact resolve eq2039891 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039891
  have eq2039962 : x = (M.op x y) := by grind
  clear eq2039961
  have eq2040263 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2039962 eq20
    | exact resolve eq20 eq2039962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2040266 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2039962 eq56
    | exact resolve eq56 eq2039962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2040369 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq2039962 eq1364
    | exact resolve eq1364 eq2039962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq2040708 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2039962 eq370023
    | exact resolve eq370023 eq2039962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370023
  have eq2040771 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2040708
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2040708
    | exact resolve eq2040708 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2040708
  have eq2040928 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2040263
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2040263
    | exact resolve eq2040263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040263
  have eq2040930 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2039962 eq2040771
    | exact resolve eq2040771 eq2039962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040771
  have eq2040961 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2040928 eq26
    | exact resolve eq26 eq2040928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2058320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2040928 eq2040930
    | exact resolve eq2040930 eq2040928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040930
  have eq2058321 : x = (M.op y y) := by
    first
    | (have r₁ := eq2058320
       have r₂ := eq27
       grind)
    | exact resolve eq2058320 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058320
  have eq2058323 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq2058321
       grind)
    | exact superpose eq2058321 eq104
    | exact resolve eq104 eq2058321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq2058650 : x ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2058321
       grind)
    | exact superpose eq2058321 eq13
    | (have j0 := eq13 y y
       grind)
    | exact resolve eq13 eq2058321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2059617 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2058323
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2058323
    | exact resolve eq2058323 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058323
  have eq2059851 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2040928 eq2059617
    | exact resolve eq2059617 eq2040928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059617
  have eq2103349 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq7686 eq2059851
    | exact resolve eq2059851 eq7686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7686
  have eq2103362 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq2059851 eq88
    | exact resolve eq88 eq2059851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059851
  have eq2103761 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq2103362
    | exact resolve eq2103362 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2103362
  have eq2103785 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq2039962 eq2103761
    | exact resolve eq2103761 eq2039962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103761
  have eq2105659 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq655925 y (M.op x (M.op X0 X0))
       have i₂ := eq2040266 X0
       grind)
    | exact superpose eq2040266 eq655925
    | exact resolve eq655925 eq2040266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655925
  have eq2105703 : ∀ X0 : G, (k X0 (M.op (M.op x (M.op X0 X0)) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1290520 y (M.op x (M.op X0 X0))
       have i₂ := eq2040266 X0
       grind)
    | exact superpose eq2040266 eq1290520
    | exact resolve eq1290520 eq2040266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290520 eq2040266
  have eq2105744 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2105703 X0
       have i₂ := eq428 X0 x
       grind)
    | exact superpose eq428 eq2105703
    | exact resolve eq2105703 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq2105703
  have eq2105784 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2039962 eq2105659
    | exact resolve eq2105659 eq2039962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039962 eq2105659
  have eq2106678 : (σ y) ≠ (σ y) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq7658 (M.op y y)
       have i₂ := eq2105744 y
       grind)
    | exact superpose eq2105744 eq7658
    | (have j0 := eq7658 (M.op y y)
       grind)
    | exact resolve eq7658 eq2105744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7658 eq2105744
  have eq2107274 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | (have r₁ := eq2106678
       have r₂ := eq24
       grind)
    | exact resolve eq2106678 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106678
  have eq2107554 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq2107274
       have i₂ := eq2058321
       grind)
    | exact superpose eq2058321 eq2107274
    | exact resolve eq2107274 eq2058321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107274
  have eq2107700 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq2107554
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2107554
    | exact resolve eq2107554 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107554
  have eq2107820 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | exact superpose eq26 eq2107700
    | exact resolve eq2107700 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107700
  have eq2107860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | exact superpose eq2040928 eq2107820
    | exact resolve eq2107820 eq2040928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107820
  have eq2107889 : (σ y) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | (have r₁ := eq2107860
       have r₂ := eq27
       grind)
    | exact resolve eq2107860 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107860
  have eq2107913 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2107889
       have i₂ := eq2058321
       grind)
    | exact superpose eq2058321 eq2107889
    | exact resolve eq2107889 eq2058321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058321 eq2107889
  have eq2107926 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2107913
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2107913
    | exact resolve eq2107913 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107913
  have eq2107935 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2107926
    | exact resolve eq2107926 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2107926
  have eq2107947 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2107935 eq27
    | exact resolve eq27 eq2107935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2268834 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (M.op X0 (M.op y (M.op x X0)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq258542 X0 X1 X2 X0
       have i₂ := eq2040369 X0
       grind)
    | exact superpose eq2040369 eq258542
    | exact resolve eq258542 eq2040369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258542 eq2040369
  have eq2270901 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2268834 X0 X1 X2
       have i₂ := eq2105784 X0
       grind)
    | exact superpose eq2105784 eq2268834
    | exact resolve eq2268834 eq2105784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105784 eq2268834
  have eq2461765 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2270901 X1 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq372 X0
       grind)
    | exact superpose eq372 eq2270901
    | exact resolve eq2270901 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq2270901
  have eq3268952 : y = (τ (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2103349 eq1933833
    | exact resolve eq1933833 eq2103349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933833 eq2103349
  have eq3270432 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq88 eq3268952
    | exact resolve eq3268952 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq3268952
  have eq3270817 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq3270432
       have r₂ := eq2058650
       grind)
    | exact resolve eq3270432 eq2058650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058650 eq3270432
  have eq3271057 : (σ x) = (σ y) ∨ y = (k y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2107935 eq3270817
    | exact resolve eq3270817 eq2107935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107935 eq3270817
  have eq3271198 : (σ (M.op x y)) = (σ y) ∨ y = (k y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2040928 eq3271057
    | exact resolve eq3271057 eq2040928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271057
  have eq3271269 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq3271198
       have r₂ := eq2107947
       grind)
    | exact resolve eq3271198 eq2107947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271198
  have eq3272327 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq3271269 eq2461765
    | exact resolve eq2461765 eq3271269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461765 eq3271269
  have eq3272371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq2040961 eq3272327
    | exact resolve eq3272327 eq2040961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040961 eq3272327
  have eq3273009 : y = (k y y) := by
    first
    | (have r₁ := eq3272371
       have r₂ := eq27
       grind)
    | exact resolve eq3272371 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3272371
  have eq3273963 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2103785
       have i₂ := eq3273009
       grind)
    | exact superpose eq3273009 eq2103785
    | exact resolve eq2103785 eq3273009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103785 eq3273009
  have eq3274275 : x = y := by grind
  clear eq3273963
  have eq3274998 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3274275
       grind)
    | exact superpose eq3274275 eq24
    | exact resolve eq24 eq3274275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3274275
  have eq3276433 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3274998
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3274998
    | exact resolve eq3274998 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3274998
  have eq3276746 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2040928 eq3276433
    | exact resolve eq3276433 eq2040928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040928 eq3276433
  have eq3276884 : False := by grind
  exact eq3276884

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq52 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq52
    | exact resolve eq52 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq85 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq85 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq85 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq89 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq15
    | exact resolve eq15 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq86 (τ X0)
       grind)
    | exact superpose eq86 eq18
    | exact resolve eq18 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq96 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq89
    | exact resolve eq89 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq96
    | exact resolve eq96 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq96
  have eq110 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0) (σ X0)
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq52
    | exact resolve eq52 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq9
    | exact resolve eq9 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq100 (M.op X0 X0)
       grind)
    | exact superpose eq100 eq110
    | exact resolve eq110 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq119
    | exact resolve eq119 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq10
    | exact resolve eq10 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq135 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq143 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1
       have i₂ := eq100 X1
       grind)
    | exact superpose eq100 eq135
    | (have j0 := eq135 X0 X1
       grind)
    | exact resolve eq135 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq145 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq154 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq9
    | exact resolve eq9 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq51 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq52 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq51 X0 x x X3
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq51 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq9
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq202 X0 X1 X2 X3
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq202
    | exact resolve eq202 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq249 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq173 X0 X0 X0
       grind)
    | exact superpose eq173 eq173
    | exact resolve eq173 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq173 X0 X0 X0
       grind)
    | exact superpose eq173 eq173
    | exact resolve eq173 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq173 X0 X0 X0
       grind)
    | exact superpose eq173 eq9
    | exact resolve eq9 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq199 (M.op x (M.op x x)) x
       have i₂ := eq173 x x x
       grind)
    | exact superpose eq173 eq199
    | exact resolve eq199 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq347 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 x y
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq448 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op (M.op X2 X1) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq173 X0 X0 X0
       grind)
    | exact superpose eq173 eq117
    | exact resolve eq117 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq503 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq287 X2 X3
       have i₂ := eq279 X2 X0 X1
       grind)
    | exact superpose eq279 eq287
    | exact resolve eq287 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2
       have i₂ := eq279 X2 X0 X1
       grind)
    | exact superpose eq279 eq66
    | exact resolve eq66 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq507 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq173 X3 X2 X2
       have i₂ := eq279 X2 X0 X1
       grind)
    | exact superpose eq279 eq173
    | exact resolve eq173 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq506 x x (M.op X0 X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq506
    | exact resolve eq506 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq580 (τ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq580
    | exact resolve eq580 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq756 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq599 (M.op x (M.op x x))
       have i₂ := eq173 x x x
       grind)
    | exact superpose eq173 eq599
    | exact resolve eq599 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq599
  have eq832 : ∀ X0 X1 X2 : G, (τ X2) = (M.op (τ X2) (τ (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq756 X2
       have i₂ := eq279 X2 X0 X1
       grind)
    | exact superpose eq279 eq756
    | exact resolve eq756 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq2086 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (σ X0) (σ X0) X2 x
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq69
    | exact resolve eq69 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2095 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 X2 X2 X3 X4
       have i₂ := eq279 X2 X0 X1
       grind)
    | exact superpose eq279 eq69
    | exact resolve eq69 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4153 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X3 X2 X3 X2
       have i₂ := eq212 X2 X3 X0 X1
       grind)
    | exact superpose eq212 eq69
    | exact resolve eq69 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4174 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op (M.op (M.op X4 X5) (M.op X6 X6)) (M.op X6 (M.op (M.op X3 (M.op X2 X3)) (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq188 (M.op X1 (M.op X0 X1)) (M.op X0 X1) X2 X3 X4
       have i₂ := eq212 X0 X1 X2 X3
       grind)
    | exact superpose eq212 eq188
    | exact resolve eq188 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq212
  have eq4199 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op (M.op (M.op X4 X5) (M.op X6 X6)) (M.op X6 (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq4174 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq503 X0 X1 (M.op X2 X3) X3
       grind)
    | exact superpose eq503 eq4174
    | exact resolve eq4174 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4174
  have eq7940 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq347
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq347
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq347 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq7941 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq7940
  have eq7942 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op (M.op X2 X1) (σ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq832 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq832
    | exact resolve eq832 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq9915 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op X1 X2) (M.op (M.op X2 (M.op X2 X2)) (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq249 X2 X1 (τ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq249
    | exact resolve eq249 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq10706 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq260 (M.op X0 (M.op X0 X0)) X1 (M.op X2 X0)
       have i₂ := eq287 X0 X2
       grind)
    | exact superpose eq287 eq260
    | exact resolve eq260 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11190 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10706 X0 X1 X2
       have i₂ := eq52 X2 X0
       grind)
    | exact superpose eq52 eq10706
    | exact resolve eq10706 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10706
  have eq11300 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11190 X0 X1 X2
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq11190
    | exact resolve eq11190 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11190
  have eq11347 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11300 X0 X1 X2
       have i₂ := eq287 X0 X0
       grind)
    | exact superpose eq287 eq11300
    | exact resolve eq11300 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11300
  have eq11373 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11347 X0 X1 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq11347
    | exact resolve eq11347 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11347
  have eq11437 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11373 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq260 X0 x X1
       grind)
    | exact superpose eq260 eq11373
    | exact resolve eq11373 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq11373
  have eq11675 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11437 X0 X1 X2
       have i₂ := eq287 X0 X1
       grind)
    | exact superpose eq287 eq11437
    | exact resolve eq11437 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11437
  have eq11737 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11675 X0 X1 X2
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq11675
    | exact resolve eq11675 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11675
  have eq15130 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4153 (M.op X1 X1) (M.op x x) X1 (M.op X0 X0)
       have i₂ := eq51 X1 x x X0
       grind)
    | exact superpose eq51 eq4153
    | exact resolve eq4153 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4153
  have eq15330 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15130 X0 X1
       have i₂ := eq11737 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq11737 eq15130
    | exact resolve eq15130 eq11737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11737 eq15130
  have eq15967 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq15330 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq15330 eq503
    | exact resolve eq503 eq15330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15330
  have eq16028 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15967 X0 X1 X2
       have i₂ := eq52 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq52 eq15967
    | exact resolve eq15967 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15967
  have eq20381 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16028 X1 X3 (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0)
       have i₂ := eq503 (M.op X3 (M.op X1 X1)) X2 X0 (M.op X2 (M.op X3 (M.op X1 X1)))
       grind)
    | exact superpose eq503 eq16028
    | exact resolve eq16028 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq20470 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq16028 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq16028 eq69
    | exact resolve eq69 eq16028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq16028
  have eq20524 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20470 X0 X1 X2 X3
       have i₂ := eq52 X2 X3
       grind)
    | exact superpose eq52 eq20470
    | exact resolve eq20470 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20470
  have eq36943 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X2)) = (τ (M.op X0 (M.op (M.op X1 X0) (σ X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (M.op X2 X2))
       have i₂ := eq448 X2 X0 X1
       grind)
    | exact superpose eq448 eq10
    | exact resolve eq10 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq40776 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20381 X2 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3 X4
       have i₂ := eq507 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq507 eq20381
    | exact resolve eq20381 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq20381
  have eq40912 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40776 X0 X1 X2 X3 X4
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq40776
    | exact resolve eq40776 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40776
  have eq41202 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40912 X0 X1 X2 X3 X4
       have i₂ := eq20524 X2 X1 X0 X1
       grind)
    | exact superpose eq20524 eq40912
    | exact resolve eq40912 eq20524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20524 eq40912
  have eq62192 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (τ (M.op X3 (M.op (M.op X4 X3) (σ X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36943 X3 X4 X2
       have i₂ := eq279 X2 X0 X1
       grind)
    | exact superpose eq279 eq36943
    | exact resolve eq36943 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq36943
  have eq74170 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2086 X0 X1 X2
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq2086
    | exact resolve eq2086 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086
  have eq164296 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X4 X5) (M.op (M.op (M.op X6 X7) (M.op X3 X3)) (M.op (M.op X6 X7) (M.op X3 X3)))) X0) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq4199 X1 X2 X3 (M.op X0 X0) X4 X5 (M.op (M.op X6 X7) (M.op X3 X3))
       have i₂ := eq51 X3 X6 X7 X0
       grind)
    | exact superpose eq51 eq4199
    | exact resolve eq4199 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq4199
  have eq166430 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X3 (M.op X0 X0)))) = (M.op (M.op X3 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq164296 X0 X1 X2 X3 x x x x
       have i₂ := eq41202 (M.op x x) (M.op X3 X3) X0 (M.op x x) (M.op (M.op x x) (M.op X3 X3))
       grind)
    | exact superpose eq41202 eq164296
    | exact resolve eq164296 eq41202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164296
  have eq265499 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq7941
       grind)
    | exact superpose eq7941 eq10
    | exact resolve eq10 eq7941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7941
  have eq265740 : (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq265499
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq265499
    | exact resolve eq265499 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265499
  have eq265741 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq265740
  have eq444868 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) (τ (M.op X0 X0)))) (M.op (τ (τ X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq154 (M.op (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) (τ (M.op X0 X0))) X1
       have i₂ := eq9915 X0 (M.op (τ (M.op X0 X0)) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) (τ (M.op X0 X0))
       grind)
    | exact superpose eq9915 eq154
    | exact resolve eq154 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq9915
  have eq445887 : ∀ X0 X1 : G, (M.op (τ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) (M.op (τ (τ X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq444868 X0 X1
       have i₂ := eq71 (τ (M.op X0 X0))
       grind)
    | exact superpose eq71 eq444868
    | exact resolve eq444868 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq444868
  have eq446819 : ∀ X0 X1 : G, (M.op (τ (τ (M.op (M.op X0 X0) (M.op X0 X0)))) (M.op (τ (τ X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq445887 X0 X1
       have i₂ := eq129 (M.op X0 X0)
       grind)
    | exact superpose eq129 eq445887
    | exact resolve eq445887 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq445887
  have eq447381 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 (M.op X0 X0)))) (M.op (τ (τ X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq446819 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq446819
    | exact resolve eq446819 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446819
  have eq543088 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (M.op (σ (M.op X3 (M.op X3 X3))) (σ (M.op X3 (M.op X3 X3)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74170 X3 X2 X2
       have i₂ := eq166430 (σ (M.op X3 (M.op X3 X3))) X0 X1 X2
       grind)
    | exact superpose eq166430 eq74170
    | exact resolve eq74170 eq166430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74170 eq166430
  have eq544086 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (σ (M.op (M.op X3 (M.op X3 X3)) (M.op X3 (M.op X3 X3)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq543088 X0 X1 X2 X3
       have i₂ := eq100 (M.op X3 (M.op X3 X3))
       grind)
    | exact superpose eq100 eq543088
    | exact resolve eq543088 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543088
  have eq545395 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (σ (M.op (M.op X3 X3) (M.op X3 (M.op X3 X3)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq544086 X0 X1 X2 X3
       have i₂ := eq52 X3 (M.op X3 X3)
       grind)
    | exact superpose eq52 eq544086
    | exact resolve eq544086 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq544086
  have eq545953 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (σ X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq545395 X0 X1 X2 X3
       have i₂ := eq287 X3 X3
       grind)
    | exact superpose eq287 eq545395
    | exact resolve eq545395 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq545395
  have eq1231759 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (τ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 (σ X3)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (M.op X3 X3)
       have i₂ := eq545953 X1 X2 X0 X3
       grind)
    | exact superpose eq545953 eq10
    | exact resolve eq10 eq545953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545953
  have eq1478573 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (τ (M.op X0 (M.op (M.op X1 X0) (σ (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2095 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq62192 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | exact superpose eq62192 eq2095
    | exact resolve eq2095 eq62192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095 eq62192
  have eq1479413 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (τ (M.op X0 (M.op (M.op X1 X0) (σ (M.op X5 X6)))))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq1478573 X0 X1 x x x X5 X6
       have i₂ := eq41202 x X5 X6 x x
       grind)
    | exact superpose eq41202 eq1478573
    | exact resolve eq1478573 eq41202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41202 eq1478573
  have eq2977235 : ∀ X0 X1 : G, (M.op x x) = (τ (M.op (σ y) (M.op X0 (M.op (M.op X1 X0) (σ y))))) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1231759 (σ y) X0 X1 x
       have i₂ := eq265741
       grind)
    | exact superpose eq265741 eq1231759
    | exact resolve eq1231759 eq265741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265741 eq1231759
  have eq2978232 : (M.op x x) = (τ (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2977235 x x
       have i₂ := eq506 x x (σ y)
       grind)
    | exact superpose eq506 eq2977235
    | exact resolve eq2977235 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq2977235
  have eq2978446 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2978232
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2978232
    | exact resolve eq2978232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978232
  have eq4129175 : ∀ X0 : G, y = (M.op (τ (τ (M.op X0 (M.op X0 X0)))) (M.op (τ (τ X0)) (M.op x x))) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq447381 X0 y
       have i₂ := eq2978446
       grind)
    | exact superpose eq2978446 eq447381
    | exact resolve eq447381 eq2978446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978446
  have eq4130389 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq4129175 x
       have i₂ := eq447381 x x
       grind)
    | exact superpose eq447381 eq4129175
    | exact resolve eq4129175 eq447381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447381 eq4129175
  have eq4131627 : ∀ X0 X1 : G, (M.op x x) = (M.op y (τ (M.op X0 (M.op (M.op X1 X0) (σ y))))) ∨ y = (M.op x x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1479413 X0 X1 y x
       have i₂ := eq4130389
       grind)
    | exact superpose eq4130389 eq1479413
    | exact resolve eq1479413 eq4130389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479413 eq4130389
  have eq4131700 : y = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq4131627 x x
       have i₂ := eq7942 y x x
       grind)
    | exact superpose eq7942 eq4131627
    | exact resolve eq4131627 eq7942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7942 eq4131627
  have eq4131701 : y = (M.op x x) ∨ x = y := by grind
  clear eq4131700
  have eq4132087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq120 x
       have i₂ := eq4131701
       grind)
    | exact superpose eq4131701 eq120
    | exact resolve eq120 eq4131701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq4131701
  have eq4134047 : x = y := by
    first
    | (have r₁ := eq4132087
       have r₂ := eq16
       grind)
    | exact resolve eq4132087 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4132087
  have eq4134279 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4134047
       grind)
    | exact superpose eq4134047 eq16
    | exact resolve eq16 eq4134047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4134047
  have eq4134280 : False := by grind
  exact eq4134280

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq52 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq52
    | exact resolve eq52 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq85 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq85 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq85 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq89 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq15
    | exact resolve eq15 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq86 (τ X0)
       grind)
    | exact superpose eq86 eq18
    | exact resolve eq18 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq96 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq89
    | exact resolve eq89 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq96
    | exact resolve eq96 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq96
  have eq110 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0) (σ X0)
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq52
    | exact resolve eq52 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq9
    | exact resolve eq9 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq100 (M.op X0 X0)
       grind)
    | exact superpose eq100 eq110
    | exact resolve eq110 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq119
    | exact resolve eq119 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq10
    | exact resolve eq10 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq135 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq143 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1
       have i₂ := eq100 X1
       grind)
    | exact superpose eq100 eq135
    | (have j0 := eq135 X0 X1
       grind)
    | exact resolve eq135 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq145 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq171 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq51 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq52 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq51 X0 x x X3
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq51 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq9
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq200 X0 X1 X2 X3
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq200
    | exact resolve eq200 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq257 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq171 X0 X0 X0
       grind)
    | exact superpose eq171 eq171
    | exact resolve eq171 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
  have eq284 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq197 (M.op x (M.op x x)) x
       have i₂ := eq171 x x x
       grind)
    | exact superpose eq171 eq197
    | exact resolve eq197 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op (M.op X0 X1) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq334 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq333 X0 X1
       have i₂ := eq197 X1 (M.op X0 X1)
       grind)
    | exact superpose eq197 eq333
    | exact resolve eq333 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq333
  have eq338 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq334 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq334
    | exact resolve eq334 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq366 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq338
    | exact resolve eq338 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq374 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq366 X0
       have i₂ := eq284 X0 X0
       grind)
    | exact superpose eq284 eq366
    | exact resolve eq366 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq414 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 x y
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq540 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X0)) = (M.op X2 (M.op (M.op X3 X2) (σ (M.op X0 (M.op X1 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq117 (M.op X1 X0) X2 X3
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq117
    | exact resolve eq117 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op (M.op X2 X1) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq171 X0 X0 X0
       grind)
    | exact superpose eq171 eq117
    | exact resolve eq117 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2
       have i₂ := eq276 X2 X0 X1
       grind)
    | exact superpose eq276 eq66
    | exact resolve eq66 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq601 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq284 X2 X3
       have i₂ := eq276 X2 X0 X1
       grind)
    | exact superpose eq276 eq284
    | exact resolve eq284 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq171 X3 X2 X2
       have i₂ := eq276 X2 X0 X1
       grind)
    | exact superpose eq276 eq171
    | exact resolve eq171 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq598 x x (M.op X0 X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq598
    | exact resolve eq598 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq598 x x (σ (M.op X0 X0))
       have i₂ := eq117 X0 x x
       grind)
    | exact superpose eq117 eq598
    | exact resolve eq598 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq699 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq679 (τ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq679
    | exact resolve eq679 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq679
  have eq815 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq699 (M.op x (M.op x x))
       have i₂ := eq171 x x x
       grind)
    | exact superpose eq171 eq699
    | exact resolve eq699 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq699
  have eq893 : ∀ X0 X1 X2 : G, (τ X2) = (M.op (τ X2) (τ (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq815 X2
       have i₂ := eq276 X2 X0 X1
       grind)
    | exact superpose eq276 eq815
    | exact resolve eq815 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq2019 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (σ X0) (σ X0) X2 x
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq69
    | exact resolve eq69 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2028 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 X2 X2 X3 X4
       have i₂ := eq276 X2 X0 X1
       grind)
    | exact superpose eq276 eq69
    | exact resolve eq69 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2029 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 X0) X2 X3
       have i₂ := eq276 X0 X0 X1
       grind)
    | exact superpose eq276 eq69
    | exact resolve eq69 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2108 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2029 X0 X1 x x
       have i₂ := eq69 X0 X0 x x
       grind)
    | exact superpose eq69 eq2029
    | exact resolve eq2029 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029
  have eq3916 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X3 X2 X3 X2
       have i₂ := eq210 X2 X3 X0 X1
       grind)
    | exact superpose eq210 eq69
    | exact resolve eq69 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3927 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X2 X3)) = (M.op X4 (M.op (M.op X5 X4) (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq69 (M.op X2 X3) X3 X4 X5
       have i₂ := eq210 X2 X3 X0 X1
       grind)
    | exact superpose eq210 eq69
    | exact resolve eq69 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3938 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op (M.op (M.op X4 X5) (M.op X6 X6)) (M.op X6 (M.op (M.op X3 (M.op X2 X3)) (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq186 (M.op X1 (M.op X0 X1)) (M.op X0 X1) X2 X3 X4
       have i₂ := eq210 X0 X1 X2 X3
       grind)
    | exact superpose eq210 eq186
    | exact resolve eq186 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq210
  have eq3959 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) = (M.op (M.op (M.op X4 X5) (M.op X6 X6)) (M.op X6 (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3938 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq601 X0 X1 (M.op X2 X3) X3
       grind)
    | exact superpose eq601 eq3938
    | exact resolve eq3938 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3938
  have eq6655 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op (M.op X2 X1) (σ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq893 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq893
    | exact resolve eq893 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq7066 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq414
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq414
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq414 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq7067 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq7066
  have eq9234 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq257 (M.op X0 (M.op X0 X0)) X1 (M.op X2 X0)
       have i₂ := eq284 X0 X2
       grind)
    | exact superpose eq284 eq257
    | exact resolve eq257 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9290 : ∀ X0 X1 X2 : G, (k (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq374 X2
       have i₂ := eq257 X2 X0 X1
       grind)
    | exact superpose eq257 eq374
    | exact resolve eq374 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq9681 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9234 X0 X1 X2
       have i₂ := eq52 X2 X0
       grind)
    | exact superpose eq52 eq9234
    | exact resolve eq9234 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9234
  have eq9824 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9681 X0 X1 X2
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq9681
    | exact resolve eq9681 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9681
  have eq9889 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9824 X0 X1 X2
       have i₂ := eq284 X0 X0
       grind)
    | exact superpose eq284 eq9824
    | exact resolve eq9824 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9824
  have eq9919 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9889 X0 X1 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq9889
    | exact resolve eq9889 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq9889
  have eq9986 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9919 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq257 X0 x X1
       grind)
    | exact superpose eq257 eq9919
    | exact resolve eq9919 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9919
  have eq10209 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9986 X0 X1 X2
       have i₂ := eq284 X0 X1
       grind)
    | exact superpose eq284 eq9986
    | exact resolve eq9986 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9986
  have eq10270 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10209 X0 X1 X2
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq10209
    | exact resolve eq10209 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10209
  have eq13540 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3916 (M.op X1 X1) (M.op x x) X1 (M.op X0 X0)
       have i₂ := eq51 X1 x x X0
       grind)
    | exact superpose eq51 eq3916
    | exact resolve eq3916 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq13736 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13540 X0 X1
       have i₂ := eq10270 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq10270 eq13540
    | exact resolve eq13540 eq10270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10270 eq13540
  have eq14187 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13736 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq257 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq257 eq13736
    | exact resolve eq13736 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq14371 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq601 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq13736 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq13736 eq601
    | exact resolve eq601 eq13736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14424 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14371 X0 X1 X2
       have i₂ := eq52 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq52 eq14371
    | exact resolve eq14371 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14371
  have eq14523 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14187 X0 X1
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq14187
    | exact resolve eq14187 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14187
  have eq14610 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14523 X0 X1
       have i₂ := eq284 X0 X1
       grind)
    | exact superpose eq284 eq14523
    | exact resolve eq14523 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14523
  have eq14797 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14610 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq601 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq601 eq14610
    | exact resolve eq14610 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14610
  have eq15672 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13736 X2 X1
       have i₂ := eq14797 X2 X1 X0
       grind)
    | (have i₁ := eq13736 X0 X1
       have i₂ := eq14797 X0 X1 X1
       grind)
    | exact superpose eq14797 eq13736
    | exact resolve eq13736 eq14797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13736 eq14797
  have eq18564 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14424 X1 X3 (M.op (M.op X2 (M.op X3 (M.op X1 X1))) X0)
       have i₂ := eq601 (M.op X3 (M.op X1 X1)) X2 X0 (M.op X2 (M.op X3 (M.op X1 X1)))
       grind)
    | exact superpose eq601 eq14424
    | exact resolve eq14424 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq18651 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq14424 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq14424 eq69
    | exact resolve eq69 eq14424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq14424
  have eq18695 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18651 X0 X1 X2 X3
       have i₂ := eq52 X2 X3
       grind)
    | exact superpose eq52 eq18651
    | exact resolve eq18651 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18651
  have eq32800 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 (M.op (M.op X1 X0) X2))) = (M.op X3 (M.op (M.op X4 X3) (σ X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq542 X2 X3 X4
       have i₂ := eq276 X2 X0 X1
       grind)
    | exact superpose eq276 eq542
    | exact resolve eq542 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32980 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X2)) = (τ (M.op X0 (M.op (M.op X1 X0) (σ X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (M.op X2 X2))
       have i₂ := eq542 X2 X0 X1
       grind)
    | exact superpose eq542 eq10
    | exact resolve eq10 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq36642 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18564 X2 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3 X4
       have i₂ := eq604 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq604 eq18564
    | exact resolve eq18564 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq18564
  have eq36760 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36642 X0 X1 X2 X3 X4
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq36642
    | exact resolve eq36642 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36642
  have eq37040 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36760 X0 X1 X2 X3 X4
       have i₂ := eq18695 X2 X1 X0 X1
       grind)
    | exact superpose eq18695 eq36760
    | exact resolve eq36760 eq18695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18695 eq36760
  have eq62892 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (τ (M.op X3 (M.op (M.op X4 X3) (σ X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq32980 X3 X4 X2
       have i₂ := eq276 X2 X0 X1
       grind)
    | exact superpose eq276 eq32980
    | exact resolve eq32980 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq32980
  have eq74461 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2019 X0 X1 X2
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq2019
    | exact resolve eq2019 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq2019
  have eq148964 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3927 X3 X2 (M.op X1 (M.op X2 X3)) (M.op X0 X0) X4 X5
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq3927
    | exact resolve eq3927 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3927
  have eq150889 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq148964 X0 x X2 X3 X4 X5
       have i₂ := eq15672 x (M.op X2 X3) (M.op X0 X0)
       grind)
    | exact superpose eq15672 eq148964
    | exact resolve eq148964 eq15672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15672 eq148964
  have eq151572 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) = (M.op X4 (M.op (M.op X5 X4) (M.op X3 X0))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq150889 X0 X2 X3 X4 X5
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq150889
    | exact resolve eq150889 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150889
  have eq178449 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X3 (M.op X0 X0)))) = (M.op (M.op (M.op X4 X5) (M.op (M.op (M.op X6 X7) (M.op X3 X3)) (M.op (M.op X6 X7) (M.op X3 X3)))) X0) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq3959 X1 X2 X3 (M.op X0 X0) X4 X5 (M.op (M.op X6 X7) (M.op X3 X3))
       have i₂ := eq51 X3 X6 X7 X0
       grind)
    | exact superpose eq51 eq3959
    | exact resolve eq3959 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq3959
  have eq180612 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X3 (M.op X0 X0)))) = (M.op (M.op X3 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq178449 X0 X1 X2 X3 x x x x
       have i₂ := eq37040 (M.op x x) (M.op X3 X3) X0 (M.op x x) (M.op (M.op x x) (M.op X3 X3))
       grind)
    | exact superpose eq37040 eq178449
    | exact resolve eq178449 eq37040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178449
  have eq307896 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq7067
       grind)
    | exact superpose eq7067 eq10
    | exact resolve eq10 eq7067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7067
  have eq308139 : (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq307896
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq307896
    | exact resolve eq307896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307896
  have eq308140 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq308139
  have eq499629 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (M.op (σ (M.op X3 (M.op X3 X3))) (σ (M.op X3 (M.op X3 X3)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74461 X3 X2 X2
       have i₂ := eq180612 (σ (M.op X3 (M.op X3 X3))) X0 X1 X2
       grind)
    | exact superpose eq180612 eq74461
    | exact resolve eq74461 eq180612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74461 eq180612
  have eq500575 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (σ (M.op (M.op X3 (M.op X3 X3)) (M.op X3 (M.op X3 X3)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq499629 X0 X1 X2 X3
       have i₂ := eq100 (M.op X3 (M.op X3 X3))
       grind)
    | exact superpose eq100 eq499629
    | exact resolve eq499629 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499629
  have eq501844 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (σ (M.op (M.op X3 X3) (M.op X3 (M.op X3 X3)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq500575 X0 X1 X2 X3
       have i₂ := eq52 X3 (M.op X3 X3)
       grind)
    | exact superpose eq52 eq500575
    | exact resolve eq500575 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq500575
  have eq502398 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 (σ X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq501844 X0 X1 X2 X3
       have i₂ := eq284 X3 X3
       grind)
    | exact superpose eq284 eq501844
    | exact resolve eq501844 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq501844
  have eq1242696 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (τ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 (σ X3)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (M.op X3 X3)
       have i₂ := eq502398 X1 X2 X0 X3
       grind)
    | exact superpose eq502398 eq10
    | exact resolve eq10 eq502398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502398
  have eq1550127 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (τ (M.op X0 (M.op (M.op X1 X0) (σ (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2028 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq62892 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | exact superpose eq62892 eq2028
    | exact resolve eq2028 eq62892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028 eq62892
  have eq1551010 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (τ (M.op X0 (M.op (M.op X1 X0) (σ (M.op X5 X6)))))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq1550127 X0 X1 x x x X5 X6
       have i₂ := eq37040 x X5 X6 x x
       grind)
    | exact superpose eq37040 eq1550127
    | exact resolve eq1550127 eq37040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37040 eq1550127
  have eq2084957 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op X5 (M.op (M.op X6 X5) (σ (M.op X3 (M.op X3 X3))))) = (σ (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq32800 X2 x (M.op X3 (M.op X3 X3)) X5 X6
       have i₂ := eq151572 X3 x X2 X0 X1
       grind)
    | exact superpose eq151572 eq32800
    | exact resolve eq32800 eq151572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32800 eq151572
  have eq2090860 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) = (σ (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2084957 X0 X1 X2 X3 x x
       have i₂ := eq540 X3 X3 x x
       grind)
    | exact superpose eq540 eq2084957
    | exact resolve eq2084957 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq2084957
  have eq3195558 : ∀ X0 X1 : G, (M.op y y) = (τ (M.op (σ x) (M.op X0 (M.op (M.op X1 X0) (σ x))))) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1242696 (σ x) X0 X1 y
       have i₂ := eq308140
       grind)
    | exact superpose eq308140 eq1242696
    | exact resolve eq1242696 eq308140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308140 eq1242696
  have eq3196573 : (M.op y y) = (τ (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3195558 x x
       have i₂ := eq598 x x (σ x)
       grind)
    | exact superpose eq598 eq3195558
    | exact resolve eq3195558 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195558
  have eq3196809 : (M.op x x) = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3196573
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3196573
    | exact resolve eq3196573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196573
  have eq4627921 : ∀ X0 : G, y = (k (M.op x x) (M.op (M.op X0 (M.op x x)) (M.op x x))) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9290 X0 y y
       have i₂ := eq3196809
       grind)
    | exact superpose eq3196809 eq9290
    | exact resolve eq9290 eq3196809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196809
  have eq4628845 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4627921 x
       have i₂ := eq9290 x x x
       grind)
    | exact superpose eq9290 eq4627921
    | exact resolve eq4627921 eq9290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9290 eq4627921
  have eq4630359 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2108 y y
       have i₂ := eq4628845
       grind)
    | exact superpose eq4628845 eq2108
    | exact resolve eq2108 eq4628845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4628845
  have eq4631109 : x = (M.op x y) ∨ x = y := by grind
  clear eq4630359
  have eq4632008 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2108 y x
       have i₂ := eq4631109
       grind)
    | exact superpose eq4631109 eq2108
    | exact resolve eq2108 eq4631109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108
  have eq4632693 : ∀ X0 X1 : G, (M.op y y) = (M.op x (τ (M.op X0 (M.op (M.op X1 X0) (σ x))))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1551010 X0 X1 x y
       have i₂ := eq4631109
       grind)
    | exact superpose eq4631109 eq1551010
    | exact resolve eq1551010 eq4631109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551010
  have eq4632721 : ∀ X0 X1 : G, (σ (M.op y y)) = (σ (M.op x (M.op X0 (M.op (M.op X1 X0) x)))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2090860 X0 X1 x y
       have i₂ := eq4631109
       grind)
    | exact superpose eq4631109 eq2090860
    | exact resolve eq2090860 eq4631109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090860 eq4631109
  have eq4632774 : (σ x) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq4632721 x x
       have i₂ := eq598 x x x
       grind)
    | exact superpose eq598 eq4632721
    | exact resolve eq4632721 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq4632721
  have eq4632785 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq4632693 x x
       have i₂ := eq6655 x x x
       grind)
    | exact superpose eq6655 eq4632693
    | exact resolve eq4632693 eq6655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655 eq4632693
  have eq4633329 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq681 y
       have i₂ := eq4632785
       grind)
    | exact superpose eq4632785 eq681
    | exact resolve eq681 eq4632785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq4632785
  have eq4638726 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq4632774
       have i₂ := eq4632008
       grind)
    | exact superpose eq4632008 eq4632774
    | exact resolve eq4632774 eq4632008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4632008 eq4632774
  have eq4639415 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq4638726
  have eq4655513 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq4633329
       grind)
    | exact superpose eq4633329 eq16
    | exact resolve eq16 eq4633329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4633329
  have eq4656889 : x = y := by
    first
    | (have r₁ := eq4655513
       have r₂ := eq4639415
       grind)
    | exact resolve eq4655513 eq4639415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639415 eq4655513
  have eq4657448 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4656889
       grind)
    | exact superpose eq4656889 eq16
    | exact resolve eq16 eq4656889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656889
  have eq4657449 : False := by grind
  exact eq4657449

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_y_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  have eq176 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq177 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq181 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq176 (M.op sF0 sF0)
       have i₂ := eq16 sF0 sF0 sF0
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq662 X0
       grind)
    | exact superpose eq662 eq177
    | (have j1 := eq662 X0
       grind)
    | exact resolve eq177 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq179 X0 X0
       have i₂ := eq662 X0
       grind)
    | exact superpose eq662 eq179
    | (have j1 := eq662 X0
       grind)
    | exact resolve eq179 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq179 X0 X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 (M.op X1 X0)
       have i₂ := eq179 X1 X0
       grind)
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op X1 X0)
       have i₂ := eq179 X1 X0
       grind)
    | exact superpose eq179 eq176
    | exact resolve eq176 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq749 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq725 X0
       grind)
    | exact superpose eq725 eq16
    | exact resolve eq16 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq725 X0
       grind)
    | exact superpose eq725 eq13
    | (have j0 := eq13 (M.op X0 (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X0 X0)) X0
       have r₂ := eq725 X0
       grind)
    | exact resolve eq13 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq751 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq750 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq877 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq716 eq16
    | exact resolve eq16 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq886 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq877 X0
       have i₂ := eq179 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq179 eq877
    | exact resolve eq877 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq890 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq886 X0
       have i₂ := eq179 X0 X0
       grind)
    | exact superpose eq179 eq886
    | exact resolve eq886 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq998 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq182 eq179
    | exact resolve eq179 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1005 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op X0 (M.op (M.op X1 X0) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    first
    | exact superpose eq182 eq177
    | exact resolve eq177 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq2090 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq733 (M.op X0 X0) X0
       have i₂ := eq890 X0
       grind)
    | exact superpose eq890 eq733
    | exact resolve eq733 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2217 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq890 X0
       have i₂ := eq2090 X0
       grind)
    | exact superpose eq2090 eq890
    | exact resolve eq890 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2219 : ∀ X0 : G, (k (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq751 X0
       have i₂ := eq2090 X0
       grind)
    | exact superpose eq2090 eq751
    | exact resolve eq751 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq2221 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq733 X0 X0
       have i₂ := eq2090 X0
       grind)
    | exact superpose eq2090 eq733
    | exact resolve eq733 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2230 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq179 X0 (M.op X0 X0)
       have i₂ := eq2090 X0
       grind)
    | exact superpose eq2090 eq179
    | exact resolve eq179 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2261 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq2230 X0
       have i₂ := eq179 sF3 (M.op sF4 X0)
       grind)
    | exact superpose eq179 eq2230
    | exact resolve eq2230 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq2272 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2217 eq2261
    | exact resolve eq2261 eq2217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217 eq2261
  have eq2299 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq177 eq2219
    | exact resolve eq2219 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2219
  have eq2397 : ∀ X0 : G, y = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op x x))) ∨ (M.op x y) = (k x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq187 X0 y
       have i₂ := eq597
       grind)
    | exact superpose eq597 eq187
    | exact resolve eq187 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq2422 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2397 x
       have i₂ := eq1001 x sF4 x
       grind)
    | exact superpose eq1001 eq2397
    | exact resolve eq2397 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq2451 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op (σ x) (σ x)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq605 eq187
    | exact resolve eq187 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq605
  have eq2472 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2451 x
       have i₂ := eq1001 x sF4 sF2
       grind)
    | exact superpose eq1001 eq2451
    | exact resolve eq2451 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq2451
  have eq2493 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq2299 sF2
       grind)
    | exact superpose eq2299 eq90
    | exact resolve eq90 eq2299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299
  have eq3251 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq734 (M.op X0 X0) X0
       have i₂ := eq890 X0
       grind)
    | exact superpose eq890 eq734
    | exact resolve eq734 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq3259 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2272 eq734
    | exact resolve eq734 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq2272
  have eq4189 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)))) := by
    first
    | exact superpose eq3259 eq733
    | exact resolve eq733 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259
  have eq4213 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq2221 eq4189
    | exact resolve eq4189 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221 eq4189
  have eq4244 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq662 y
       have i₂ := eq4213
       grind)
    | exact superpose eq4213 eq662
    | exact resolve eq662 eq4213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4557 : y ≠ (k y y) ∨ y = (M.op (M.op x y) y) := by grind
  have eq6672 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq749 X0 X0
       grind)
    | exact superpose eq749 eq16
    | exact resolve eq16 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6692 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq998 (M.op X1 (M.op X1 X1)) X1
       have i₂ := eq749 X1 X1
       grind)
    | exact superpose eq749 eq998
    | exact resolve eq998 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq998
  have eq8154 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2422
       grind)
    | exact superpose eq2422 eq40
    | exact resolve eq40 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8159 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq8154
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8154
    | exact resolve eq8154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8154
  have eq8161 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq8159
    | exact resolve eq8159 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8159
  have eq15978 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 (M.op X1 X0)
       have i₂ := eq6672 X0 X0 X1
       grind)
    | exact superpose eq6672 eq733
    | exact resolve eq733 eq6672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6672
  have eq16030 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq733 eq15978
    | exact resolve eq15978 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq17176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq8161 eq2472
    | exact resolve eq2472 eq8161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17185 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq17176
       have r₂ := eq27
       grind)
    | exact resolve eq17176 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17176
  have eq17194 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq17185 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17185
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17185
       grind)
    | exact resolve eq13 eq17185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17211 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq17185 eq16030
    | exact resolve eq16030 eq17185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17212 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq17194
  have eq17213 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq17185 eq17211
    | exact resolve eq17211 eq17185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17185 eq17211
  have eq17231 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq17212 eq8161
    | exact resolve eq8161 eq17212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8161
  have eq17236 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq17212 eq90
    | exact resolve eq90 eq17212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq17212
  have eq17241 : y = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq17231
  have eq17245 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq17236
    | exact resolve eq17236 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17236
  have eq17250 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq17245
       have r₂ := eq13 x y
       grind)
    | exact resolve eq17245 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17245
  have eq17258 : y = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2422
       have i₂ := eq17250
       grind)
    | exact superpose eq17250 eq2422
    | exact resolve eq2422 eq17250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq17259 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq17250
       grind)
    | exact superpose eq17250 eq35
    | exact resolve eq35 eq17250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq17250
  have eq17263 : y = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17258
  have eq17267 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17259
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17259
    | exact resolve eq17259 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17259
  have eq17278 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17267 eq2472
    | exact resolve eq2472 eq17267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472 eq17267
  have eq17285 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq17278
  have eq17300 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq179 y x
       have i₂ := eq17241
       grind)
    | exact superpose eq17241 eq179
    | exact resolve eq179 eq17241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17305 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq733 x y
       have i₂ := eq17241
       grind)
    | exact superpose eq17241 eq733
    | exact resolve eq733 eq17241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq17314 : (M.op x x) = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16030 x y
       have i₂ := eq17241
       grind)
    | exact superpose eq17241 eq16030
    | exact resolve eq16030 eq17241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17316 : y = (M.op x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17241 eq17314
    | exact resolve eq17314 eq17241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17241 eq17314
  have eq17319 : y = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17305
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17305
    | exact resolve eq17305 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17305
  have eq17322 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17300
       have i₂ := eq4213
       grind)
    | exact superpose eq4213 eq17300
    | exact resolve eq17300 eq4213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17300
  have eq17326 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1007 eq17319
    | exact resolve eq17319 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17319
  have eq17328 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17322
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17322
    | exact resolve eq17322 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17322
  have eq17342 : (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq179 y x
       have i₂ := eq17263
       grind)
    | exact superpose eq17263 eq179
    | exact resolve eq179 eq17263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17356 : (M.op x x) = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16030 x y
       have i₂ := eq17263
       grind)
    | exact superpose eq17263 eq16030
    | exact resolve eq16030 eq17263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17358 : y = (M.op x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17263 eq17356
    | exact resolve eq17356 eq17263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17263 eq17356
  have eq17364 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17342
       have i₂ := eq4213
       grind)
    | exact superpose eq4213 eq17342
    | exact resolve eq17342 eq4213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213 eq17342
  have eq17370 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17364
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17364
    | exact resolve eq17364 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17364
  have eq17403 : y = (k x x) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq662 x
       have i₂ := eq17316
       grind)
    | exact superpose eq17316 eq662
    | exact resolve eq662 eq17316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17442 : x = (M.op y (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6692 x x
       have i₂ := eq17316
       grind)
    | exact superpose eq17316 eq6692
    | exact resolve eq6692 eq17316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17316
  have eq17445 : y = (k x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq17403
  have eq17446 : x = (M.op y (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17442
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17442
    | exact resolve eq17442 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17442
  have eq17474 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq181 eq17446
    | exact resolve eq17446 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq17446
  have eq17493 : (M.op x y) = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq4244 eq17328
    | exact resolve eq17328 eq4244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17500 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17328 eq4244
    | exact resolve eq4244 eq17328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17328
  have eq17549 : (M.op x y) = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17500 eq17493
    | exact resolve eq17493 eq17500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17493 eq17500
  have eq17571 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq17285 eq179
    | exact resolve eq179 eq17285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17285
  have eq17594 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq17571
    | exact resolve eq17571 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17571
  have eq17626 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq662 x
       have i₂ := eq17358
       grind)
    | exact superpose eq17358 eq662
    | exact resolve eq662 eq17358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17358
  have eq17668 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17626
  have eq17923 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17370 eq4244
    | exact resolve eq4244 eq17370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4244 eq17370
  have eq17956 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17923
  have eq17991 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq17445
       grind)
    | exact superpose eq17445 eq39
    | exact resolve eq39 eq17445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17445
  have eq17993 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17991
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17991
    | exact resolve eq17991 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17991
  have eq17997 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17993
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17993
    | exact resolve eq17993 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17993
  have eq18382 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq17594 eq662
    | exact resolve eq662 eq17594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17594
  have eq18423 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18382
  have eq18488 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq17668
       grind)
    | exact superpose eq17668 eq39
    | exact resolve eq39 eq17668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17668
  have eq18490 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18488
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18488
    | exact resolve eq18488 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18488
  have eq18494 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18490
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18490
    | exact resolve eq18490 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18490
  have eq18822 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq17956
       grind)
    | exact superpose eq17956 eq40
    | exact resolve eq40 eq17956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq17956
  have eq18824 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18822
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18822
    | exact resolve eq18822 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18822
  have eq18828 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq18824
    | exact resolve eq18824 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18824
  have eq19112 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18423 eq115
    | exact resolve eq115 eq18423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq19361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18828 eq18423
    | exact resolve eq18423 eq18828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18423 eq18828
  have eq19368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq19361
  have eq19375 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19368
       have r₂ := eq27
       grind)
    | exact resolve eq19368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19368
  have eq19379 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19375 eq27
    | exact resolve eq27 eq19375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19546 : y ≠ (τ (M.op (σ x) (σ y))) ∨ y = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4557
       have i₂ := eq19112
       grind)
    | exact superpose eq19112 eq4557
    | exact resolve eq4557 eq19112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq19555 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ y = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19375 eq19546
    | exact resolve eq19546 eq19375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19546
  have eq19561 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19375 eq19555
    | exact resolve eq19555 eq19375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19375 eq19555
  have eq19594 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq17213 eq662
    | exact resolve eq662 eq17213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17213
  have eq19636 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq19594
  have eq19657 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq18494 eq19636
    | exact resolve eq19636 eq18494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19636
  have eq20021 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq19657 eq97
    | exact resolve eq97 eq19657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq19657
  have eq20031 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq31 eq20021
    | exact resolve eq20021 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20021
  have eq20237 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq20031 eq179
    | exact resolve eq179 eq20031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq20251 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq20031 eq16030
    | exact resolve eq16030 eq20031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16030
  have eq20257 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq20031 eq20251
    | exact resolve eq20251 eq20031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20031 eq20251
  have eq20851 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17997 eq677
    | (have j0 := eq677 (σ x)
       grind)
    | exact resolve eq677 eq17997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20895 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2090 eq20851
    | exact resolve eq20851 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090 eq20851
  have eq31308 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq19112
       have i₂ := eq17549
       grind)
    | exact superpose eq17549 eq19112
    | exact resolve eq19112 eq17549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17549 eq19112
  have eq31314 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq31308
  have eq31321 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31314
       have r₂ := eq19561
       grind)
    | exact resolve eq31314 eq19561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19561 eq31314
  have eq31345 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31321 eq17326
    | exact resolve eq17326 eq31321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17326 eq31321
  have eq31455 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31345
  have eq31507 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17474 eq31455
    | exact resolve eq31455 eq17474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17474 eq31455
  have eq31508 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31507
  have eq38030 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17997 eq712
    | (have j0 := eq712 (σ x)
       grind)
    | exact resolve eq712 eq17997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38156 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq38030
    | exact resolve eq38030 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38030
  have eq38176 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31508 eq38156
    | exact resolve eq38156 eq31508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31508 eq38156
  have eq38574 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq38176 eq6692
    | exact resolve eq6692 eq38176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38176
  have eq38596 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20895 eq38574
    | exact resolve eq38574 eq20895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20895 eq38574
  have eq38597 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq38596
  have eq38727 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38597 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq38597
       grind)
    | exact resolve eq13 eq38597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38597
  have eq38752 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq38727
  have eq38851 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38752 eq17997
    | exact resolve eq17997 eq38752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17997
  have eq38853 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38752 eq18494
    | exact resolve eq18494 eq38752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18494 eq38752
  have eq38870 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq38853
  have eq38872 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq38851
  have eq38881 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq38870
       have r₂ := eq19379
       grind)
    | exact resolve eq38870 eq19379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19379 eq38870
  have eq38883 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38872 eq31
    | exact resolve eq31 eq38872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38872
  have eq39075 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq38883
    | exact resolve eq38883 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38883
  have eq39076 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq39075
  have eq39092 : (M.op x y) = (τ (σ y)) ∨ x = y := by
    first
    | exact superpose eq39076 eq28
    | exact resolve eq28 eq39076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39076
  have eq39213 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq39092
    | exact resolve eq39092 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39092
  have eq39224 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq39213
       grind)
    | exact superpose eq39213 eq18
    | exact resolve eq18 eq39213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39261 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3251 X0
       have i₂ := eq39213
       grind)
    | exact superpose eq39213 eq3251
    | exact resolve eq3251 eq39213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251
  have eq39308 : x ≠ (M.op x y) ∨ x = y := by grind
  have eq39343 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq39224 eq20237
    | exact resolve eq20237 eq39224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20237
  have eq39390 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by grind
  clear eq39343
  have eq39395 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq38881 eq39390
    | exact resolve eq39390 eq38881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38881 eq39390
  have eq47018 : (M.op (M.op x y) (M.op (M.op x y) x)) = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq39261 x
       have i₂ := eq20257
       grind)
    | exact superpose eq20257 eq39261
    | exact resolve eq39261 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47054 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq6692 X0 X1
       have i₂ := eq39261 X0
       grind)
    | (have i₁ := eq6692 (M.op x y) X1
       have i₂ := eq39261 (M.op x y)
       grind)
    | exact superpose eq39261 eq6692
    | exact resolve eq6692 eq39261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6692 eq39261
  have eq47226 : (M.op (M.op x y) (M.op (M.op x y) x)) = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x x) := by grind
  clear eq47018
  have eq47301 : (M.op (M.op x y) (M.op (M.op x y) x)) = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq39213 eq47226
    | exact resolve eq47226 eq39213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47226
  have eq47338 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq39224 eq47301
    | exact resolve eq47301 eq39224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47301
  have eq48705 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq47054 x x
       have i₂ := eq20257
       grind)
    | exact superpose eq20257 eq47054
    | exact resolve eq47054 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20257 eq47054
  have eq49086 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) x))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k x x) := by grind
  clear eq48705
  have eq49214 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq39213 eq49086
    | exact resolve eq49086 eq39213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39213 eq49086
  have eq49276 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq47338 eq49214
    | exact resolve eq49214 eq47338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47338 eq49214
  have eq49298 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq39395 eq49276
    | exact resolve eq49276 eq39395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39395 eq49276
  have eq49308 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq49298
       have r₂ := eq39308
       grind)
    | exact resolve eq49298 eq39308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49298
  have eq49334 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq712 x
       have i₂ := eq49308
       grind)
    | exact superpose eq49308 eq712
    | (have j0 := eq712 x
       grind)
    | exact resolve eq712 eq49308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq49338 : x = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq677 x
       have i₂ := eq49308
       grind)
    | exact superpose eq49308 eq677
    | (have j0 := eq677 x
       grind)
    | exact resolve eq677 eq49308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq49354 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1007 eq49338
    | exact resolve eq49338 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq49338
  have eq49357 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq39224 eq49334
    | exact resolve eq49334 eq39224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39224 eq49334
  have eq87176 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq49357 eq1005
    | exact resolve eq1005 eq49357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq87279 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq49354 eq87176
    | exact resolve eq87176 eq49354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49354 eq87176
  have eq87352 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq49357 eq87279
    | exact resolve eq87279 eq49357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49357 eq87279
  have eq87394 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq87352
       have r₂ := eq39308
       grind)
    | exact resolve eq87352 eq39308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87352
  have eq87514 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq87394
       grind)
    | exact superpose eq87394 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq87394
       grind)
    | exact resolve eq13 eq87394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87394
  have eq87559 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq87514
  have eq87613 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq49308 eq87559
    | exact resolve eq87559 eq49308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49308 eq87559
  have eq87658 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq87613
       have r₂ := eq39308
       grind)
    | exact resolve eq87613 eq39308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39308 eq87613
  have eq87688 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq87658 eq31
    | exact resolve eq31 eq87658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq87658
  have eq88019 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq87688
    | exact resolve eq87688 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87688
  have eq88020 : x = y := by grind
  clear eq88019
  have eq88099 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq88020
       grind)
    | exact superpose eq88020 eq18
    | exact resolve eq18 eq88020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq88100 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq88020
       grind)
    | exact superpose eq88020 eq24
    | exact resolve eq24 eq88020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq88020
  have eq88186 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq88100
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq88100
    | exact resolve eq88100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88100
  have eq88187 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq88186 eq26
    | exact resolve eq26 eq88186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq88186
  have eq88513 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq662 x
       have i₂ := eq88099
       grind)
    | exact superpose eq88099 eq662
    | exact resolve eq662 eq88099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88576 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq88099
       grind)
    | exact superpose eq88099 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq88099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88099
  have eq88704 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq88187 eq2493
    | exact resolve eq2493 eq88187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493
  have eq88743 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq88187 eq662
    | exact resolve eq662 eq88187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq88187
  have eq92368 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq88513
       grind)
    | exact superpose eq88513 eq39
    | exact resolve eq39 eq88513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92388 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92368
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92368
    | exact resolve eq92368 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92368
  have eq92392 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq92388
    | exact resolve eq92388 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92388
  have eq92472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92392 eq88743
    | exact resolve eq88743 eq92392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92392
  have eq92497 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq92472
       have r₂ := eq27
       grind)
    | exact resolve eq92472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92472
  have eq92742 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92497 eq88704
    | exact resolve eq88704 eq92497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88704 eq92497
  have eq92796 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq92742
    | exact resolve eq92742 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq92742
  have eq92880 : x = (k x x) := by
    first
    | (have r₁ := eq92796
       have r₂ := eq88576
       grind)
    | exact resolve eq92796 eq88576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88576 eq92796
  have eq92947 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88513
       have i₂ := eq92880
       grind)
    | exact superpose eq92880 eq88513
    | exact resolve eq88513 eq92880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88513
  have eq92953 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq92880
       grind)
    | exact superpose eq92880 eq39
    | exact resolve eq39 eq92880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq92880
  have eq92962 : x = (M.op x y) := by grind
  clear eq92947
  have eq92981 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq92953
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92953
    | exact resolve eq92953 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92953
  have eq93003 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq92962
       grind)
    | exact superpose eq92962 eq22
    | exact resolve eq22 eq92962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq92962
  have eq93464 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq93003 eq20
    | exact resolve eq20 eq93003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq93003
  have eq94122 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq92981 eq88743
    | exact resolve eq88743 eq92981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88743 eq92981
  have eq94134 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq94122
  have eq94162 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq94134 eq27
    | exact resolve eq27 eq94134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq94134
  have eq94520 : False := by grind
  exact eq94520

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq64 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op (M.op X2 X1) (M.op X0 X0))) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq53 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq53
    | exact resolve eq53 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq98 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq147 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X1
       grind)
    | exact superpose eq74 eq98
    | exact resolve eq98 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq210 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq147
    | exact resolve eq147 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq283 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq153 X2 X3
       have i₂ := eq148 X2 X0 X1
       grind)
    | exact superpose eq148 eq153
    | exact resolve eq153 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X0) X2)) (M.op X2 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74 X2 X3
       have i₂ := eq148 X2 X0 X1
       grind)
    | exact superpose eq148 eq74
    | exact resolve eq74 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X2
       have i₂ := eq148 X2 X0 X1
       grind)
    | exact superpose eq148 eq72
    | exact resolve eq72 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq287 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2
       have i₂ := eq148 X2 X0 X1
       grind)
    | exact superpose eq148 eq67
    | exact resolve eq67 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq287 (M.op X0 (M.op X0 X0)) X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq287
    | exact resolve eq287 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq287 (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X2 X2)) X1
       have i₂ := eq74 X2 X0
       grind)
    | exact superpose eq74 eq287
    | exact resolve eq287 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq287 x x (M.op X0 X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq287
    | exact resolve eq287 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq348 X0
       grind)
    | exact superpose eq348 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq348 X0
       grind)
    | exact resolve eq12 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq394 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq381 (M.op x (M.op x x))
       have i₂ := eq74 x x
       grind)
    | exact superpose eq74 eq381
    | exact resolve eq381 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op (M.op X1 X0) X2)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq394 X2
       have i₂ := eq148 X2 X0 X1
       grind)
    | exact superpose eq148 eq394
    | exact resolve eq394 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq425 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X2)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq403 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1)) X2
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq403
    | exact resolve eq403 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq464 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 y x
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 y x
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq84 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq12 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq510 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq466 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq466 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq466 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq466 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq513 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq510
    | (have j0 := eq510 X0 X1
       grind)
    | exact resolve eq510 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq856 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 X1 X2
       have i₂ := eq53 (M.op X2 X1) (M.op X0 X0)
       grind)
    | exact superpose eq53 eq64
    | (have j0 := eq64 X0 X1 X2
       grind)
    | (have r₁ := eq64 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq64 (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq64 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq971 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op X1 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq856 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq992 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X2) X0)) (M.op X2 (M.op (M.op X3 X2) X0)))) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq425 (M.op X2 (M.op (M.op X3 X2) X0)) X1 X0
       have i₂ := eq286 X2 X3 X0
       grind)
    | exact superpose eq286 eq425
    | exact resolve eq425 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq425
  have eq1037 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X1 (M.op (M.op (M.op X3 X2) X0) (M.op X2 (M.op (M.op X3 X2) X0)))) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq992 X0 X1 X2 X3
       have i₂ := eq53 X2 (M.op (M.op X3 X2) X0)
       grind)
    | exact superpose eq53 eq992
    | exact resolve eq992 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1044 : ∀ X0 X1 : G, (k (M.op (M.op X1 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1037 X0 X1 x x
       have i₂ := eq283 x x X0 (M.op x x)
       grind)
    | exact superpose eq283 eq1037
    | exact resolve eq1037 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1406 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X2 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X2 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1440 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 (M.op X1 X0) X2 X3
       have i₂ := eq148 X0 X0 X1
       grind)
    | exact superpose eq148 eq70
    | exact resolve eq70 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq1449 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq70 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1512 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1440 X0 X1 x x
       have i₂ := eq70 X0 X0 x x
       grind)
    | exact superpose eq70 eq1440
    | exact resolve eq1440 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440
  have eq1949 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X1) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq971 X0 X1
       have i₂ := eq1044 X1 X0
       grind)
    | exact superpose eq1044 eq971
    | exact resolve eq971 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq1044
  have eq1998 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 (M.op X0 X0) (M.op X1 X0) X2 X3
       have i₂ := eq1949 X1 X0
       grind)
    | exact superpose eq1949 eq70
    | exact resolve eq70 eq1949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1949
  have eq2483 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X2 X2))) = (M.op (M.op X5 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1998 (M.op X2 X2) X5 X3 X4
       have i₂ := eq1998 X2 X2 X0 X1
       grind)
    | exact superpose eq1998 eq1998
    | exact resolve eq1998 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2573 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X2 X2) X3 X4
       have i₂ := eq1998 X2 X2 X0 X1
       grind)
    | exact superpose eq1998 eq9
    | exact resolve eq9 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2669 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X5 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq2483 X0 X1 X2 x x X5
       have i₂ := eq9 X2 x x
       grind)
    | exact superpose eq9 eq2483
    | exact resolve eq2483 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483
  have eq5770 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq464
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq464
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq464 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq5771 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq5770
  have eq6263 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq513 X0 (M.op X0 X0)
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq513
    | (have j0 := eq513 X0 (M.op X0 X0)
       grind)
    | exact resolve eq513 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq513
  have eq6300 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6263
  have eq6301 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6300 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq6357 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq348 (σ X0)
       have i₂ := eq6301 X0
       grind)
    | exact superpose eq6301 eq348
    | exact resolve eq348 eq6301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq13001 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X4 (M.op X4 X4)) (M.op X4 (M.op (M.op X2 X2) (M.op X0 (M.op (M.op X1 X0) X2))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1406 X0 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq1998 X0 X1 X2 x
       grind)
    | exact superpose eq1998 eq1406
    | exact resolve eq1406 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406 eq1998
  have eq13303 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X4 (M.op X4 X4)) (M.op X4 X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq13001 X0 X1 X2 X4
       have i₂ := eq283 X0 X1 X2 X2
       grind)
    | exact superpose eq283 eq13001
    | exact resolve eq13001 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13001
  have eq13823 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1449 X0 (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq1449
    | exact resolve eq1449 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21653 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X2 (M.op (M.op X3 (M.op (M.op X4 X3) X1)) (M.op X3 (M.op (M.op X4 X3) X1)))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq332 (M.op X3 (M.op (M.op X4 X3) X1)) (M.op X1 (M.op X0 X0)) X2
       have i₂ := eq284 X3 X4 X1 X0
       grind)
    | exact superpose eq284 eq332
    | exact resolve eq332 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq332
  have eq21723 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 (M.op (M.op X3 (M.op (M.op X4 X3) X1)) (M.op X3 (M.op (M.op X4 X3) X1)))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21653 X0 X1 X2 X3 X4
       have i₂ := eq13823 X0 X1 (M.op X2 (M.op (M.op X3 (M.op (M.op X4 X3) X1)) (M.op X3 (M.op (M.op X4 X3) X1))))
       grind)
    | exact superpose eq13823 eq21653
    | exact resolve eq21653 eq13823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13823 eq21653
  have eq21826 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 (M.op (M.op (M.op X4 X3) X1) (M.op X3 (M.op (M.op X4 X3) X1)))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21723 X0 X1 X2 X3 X4
       have i₂ := eq53 X3 (M.op (M.op X4 X3) X1)
       grind)
    | exact superpose eq53 eq21723
    | exact resolve eq21723 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21723
  have eq21870 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21826 X0 X1 X2 x x
       have i₂ := eq283 x x X1 (M.op x x)
       grind)
    | exact superpose eq283 eq21826
    | exact resolve eq21826 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21826
  have eq22000 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21870 (M.op X1 X0) (M.op X1 X1) x
       have i₂ := eq210 X0 x X1
       grind)
    | exact superpose eq210 eq21870
    | exact resolve eq21870 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq21870
  have eq22405 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22000 X0 X1
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq22000
    | exact resolve eq22000 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22000
  have eq22543 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22405 X0 X1
       have i₂ := eq153 X0 X1
       grind)
    | exact superpose eq153 eq22405
    | exact resolve eq22405 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq22405
  have eq22835 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22543 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq283 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq283 eq22543
    | exact resolve eq22543 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq22912 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq287 (M.op X0 (M.op X2 X0)) (M.op X2 X2) X1
       have i₂ := eq22543 X0 X2
       grind)
    | exact superpose eq22543 eq287
    | exact resolve eq287 eq22543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq23286 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22835 X2 (M.op X0 (M.op X1 X0)) (M.op X1 X1)
       have i₂ := eq22543 X0 X1
       grind)
    | exact superpose eq22543 eq22835
    | exact resolve eq22835 eq22543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22543
  have eq23382 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22835 X2 X1 X0
       have i₂ := eq22835 X2 X1 X3
       grind)
    | (have i₁ := eq22835 X0 X1 X2
       have i₂ := eq22835 X0 X1 X1
       grind)
    | exact superpose eq22835 eq22835
    | exact resolve eq22835 eq22835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22835
  have eq24392 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23286 X0 X1 X2
       have i₂ := eq53 X0 (M.op X1 X0)
       grind)
    | exact superpose eq53 eq23286
    | exact resolve eq23286 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23286
  have eq24537 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24392 X0 X1 X2
       have i₂ := eq1449 X0 X1 X0
       grind)
    | exact superpose eq1449 eq24392
    | exact resolve eq24392 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449 eq24392
  have eq24638 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X3 (M.op X1 (M.op X0 X0))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23382 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0)) X2 X3
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq23382
    | exact resolve eq23382 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq28188 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22912 X2 X3 X1
       have i₂ := eq23382 X2 (M.op X1 X2) (M.op X2 X3) X0
       grind)
    | (have i₁ := eq22912 X2 X3 X1
       have i₂ := eq23382 X0 (M.op X1 X2) (M.op X2 X3) X2
       grind)
    | exact superpose eq23382 eq22912
    | exact resolve eq22912 eq23382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22912 eq23382
  have eq36534 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24638 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X4 X2 X3
       have i₂ := eq2669 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq2669 eq24638
    | exact resolve eq24638 eq2669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2669 eq24638
  have eq37238 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36534 X0 X1 X2 X3 X4
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq36534
    | exact resolve eq36534 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq36534
  have eq37334 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X1))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq37238 X0 X1 X2 X3 X4
       have i₂ := eq24537 X1 X0 X2
       grind)
    | exact superpose eq24537 eq37238
    | exact resolve eq37238 eq24537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24537 eq37238
  have eq70862 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5771
       have i₂ := eq6301 y
       grind)
    | exact superpose eq6301 eq5771
    | exact resolve eq5771 eq6301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5771
  have eq236685 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2573 (M.op X2 (M.op X3 X4)) X1 X5 X4 X3
       have i₂ := eq13303 (M.op X3 X4) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5) X0
       grind)
    | exact superpose eq13303 eq2573
    | exact resolve eq2573 eq13303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573 eq13303
  have eq238036 : ∀ X0 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X4 X5)))) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq236685 X0 x x x X4 X5
       have i₂ := eq37334 x X4 X5 x x
       grind)
    | exact superpose eq37334 eq236685
    | exact resolve eq236685 eq37334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236685
  have eq1131294 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X2 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))))) (M.op X2 (M.op X4 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq238036 X2 X4 X3
       have i₂ := eq238036 X1 X0 X2
       grind)
    | exact superpose eq238036 eq238036
    | exact resolve eq238036 eq238036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131849 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (σ x)))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq238036 X0 (σ x) (σ y)
       have i₂ := eq70862
       grind)
    | exact superpose eq70862 eq238036
    | exact resolve eq238036 eq70862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70862 eq238036
  have eq1136762 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1131849 x
       have i₂ := eq326 x (σ x)
       grind)
    | exact superpose eq326 eq1131849
    | exact resolve eq1131849 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq1131849
  have eq1137253 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X1 (M.op X0 X2)) (M.op X2 (M.op X4 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1131294 X0 X1 X2 X3 X4
       have i₂ := eq37334 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2)) (M.op X2 (M.op X4 X3)) X2 X0
       grind)
    | exact superpose eq37334 eq1131294
    | exact resolve eq1131294 eq37334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37334 eq1131294
  have eq1138050 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1136762
       have i₂ := eq6301 y
       grind)
    | exact superpose eq6301 eq1136762
    | exact resolve eq1136762 eq6301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6301 eq1136762
  have eq1138051 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1138050
  have eq1692162 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1138051
       grind)
    | exact superpose eq1138051 eq10
    | exact resolve eq10 eq1138051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138051
  have eq1693432 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1692162
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1692162
    | exact resolve eq1692162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692162
  have eq1693433 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1693432
  have eq1694328 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1512 y y
       have i₂ := eq1693433
       grind)
    | exact superpose eq1693433 eq1512
    | exact resolve eq1512 eq1693433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512 eq1693433
  have eq1694799 : x = (M.op x y) := by grind
  clear eq1694328
  have eq1695783 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op x (M.op (M.op X0 (M.op X1 X2)) (M.op X2 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1137253 X1 X0 X2 y x
       have i₂ := eq1694799
       grind)
    | exact superpose eq1694799 eq1137253
    | exact resolve eq1137253 eq1694799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137253
  have eq1695791 : x = (M.op y y) := by
    first
    | (have i₁ := eq1695783 x x x
       have i₂ := eq28188 x x x x
       grind)
    | exact superpose eq28188 eq1695783
    | exact resolve eq1695783 eq28188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28188 eq1695783
  have eq1696126 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6357 y
       have i₂ := eq1695791
       grind)
    | exact superpose eq1695791 eq6357
    | exact resolve eq6357 eq1695791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6357 eq1695791
  have eq1747184 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1696126
       grind)
    | exact superpose eq1696126 eq16
    | exact resolve eq16 eq1696126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696126
  have eq1748007 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1747184
       have i₂ := eq1694799
       grind)
    | exact superpose eq1694799 eq1747184
    | exact resolve eq1747184 eq1694799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694799 eq1747184
  have eq1748008 : False := by grind
  exact eq1748008

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxy_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
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
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq78 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq207 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq51 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq474 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq13
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  have eq560 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq563 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq565
    | exact resolve eq565 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq571 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq563 X0 X1 X2 X3
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq563
    | exact resolve eq563 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq563
  have eq742 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1344 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq529 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq529 X0 X0 X0
       grind)
    | exact superpose eq529 eq529
    | exact resolve eq529 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1374 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq529 X0 X0 X0
       grind)
    | exact superpose eq529 eq51
    | exact resolve eq51 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1375 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq529 X0 X0 X0
       grind)
    | exact superpose eq529 eq52
    | exact resolve eq52 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1619 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq473 X0
       have i₂ := eq1374 X0
       grind)
    | exact superpose eq1374 eq473
    | exact resolve eq473 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1646 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1374 eq476
    | exact resolve eq476 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1657 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq476 eq1646
    | exact resolve eq1646 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1690 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq51 eq1619
    | exact resolve eq1619 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1619
  have eq1886 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1375 eq476
    | exact resolve eq476 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1897 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq476 eq1886
    | exact resolve eq1886 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq1886
  have eq5151 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq571 X0 X1 X2 X3
       have i₂ := eq570 X0 X1
       grind)
    | exact superpose eq570 eq571
    | exact resolve eq571 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq571
  have eq5386 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op y (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 (M.op x y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq477 (M.op x sF0) X0
       have i₂ := eq5151 X0 (M.op x sF0) sF0 x
       grind)
    | exact superpose eq5151 eq477
    | exact resolve eq477 eq5151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq5151
  have eq6264 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq78
    | (have j0 := eq78 y
       grind)
    | exact resolve eq78 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq6289 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6264
  have eq6295 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6289
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq6289
    | exact resolve eq6289 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq6289
  have eq6305 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6295
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6295 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6295
  have eq6312 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6305 eq104
    | exact resolve eq104 eq6305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq16349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq16350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16349
    | exact resolve eq16349 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16349
  have eq16355 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16350
       have r₂ := eq28
       grind)
    | exact resolve eq16350 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16350
  have eq16357 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16355
    | exact resolve eq16355 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16355
  have eq16391 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16357 eq1690
    | exact resolve eq1690 eq16357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16357
  have eq16438 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16391
    | exact resolve eq16391 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16391
  have eq16439 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16438
  have eq16477 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1690 y
       have i₂ := eq16439
       grind)
    | exact superpose eq16439 eq1690
    | exact resolve eq1690 eq16439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16439
  have eq16528 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16477
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16477
    | exact resolve eq16477 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16477
  have eq16529 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16528
  have eq16537 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16529 eq52
    | exact resolve eq52 eq16529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq16566 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16529 eq1897
    | exact resolve eq1897 eq16529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq16575 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq16566
    | exact resolve eq16566 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16566
  have eq16835 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6305 eq105
    | exact resolve eq105 eq6305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq6305
  have eq18039 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16575 eq16537
    | exact resolve eq16537 eq16575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16537 eq16575
  have eq18081 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq18039
  have eq18111 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16529 eq18081
    | exact resolve eq18081 eq16529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16529 eq18081
  have eq18147 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq18111
  have eq18164 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq18147 eq53
    | exact resolve eq53 eq18147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq18147
  have eq18209 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18164 x x
       have i₂ := eq560 sF3 (M.op x x)
       grind)
    | exact superpose eq560 eq18164
    | exact resolve eq18164 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18164
  have eq18218 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18209 eq6312
    | exact resolve eq6312 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209
  have eq18304 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq18218
    | exact resolve eq18218 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18218
  have eq18329 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq18304
       grind)
    | exact superpose eq18304 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18330 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq18329
  have eq76671 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq18330
       grind)
    | exact superpose eq18330 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq18330
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18330
       grind)
    | exact resolve eq13 eq18330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76732 : x ≠ y ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq18330
  have eq76736 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq76671
  have eq79134 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18304
       have i₂ := eq76736
       grind)
    | exact superpose eq76736 eq18304
    | exact resolve eq18304 eq76736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18304 eq76736
  have eq79158 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq79134
  have eq79174 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq79158
       have r₂ := eq76732
       grind)
    | exact resolve eq79158 eq76732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76732 eq79158
  have eq79254 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1690 y
       have i₂ := eq79174
       grind)
    | exact superpose eq79174 eq1690
    | exact resolve eq1690 eq79174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79174
  have eq79362 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79254
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79254
    | exact resolve eq79254 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79254
  have eq79363 : x = (M.op x y) := by grind
  clear eq79362
  have eq79392 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq79363 eq21
    | exact resolve eq21 eq79363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq79429 : (M.op y x) = (M.op x x) := by
    first
    | exact superpose eq79363 eq207
    | exact resolve eq207 eq79363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq79484 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq79363 eq1657
    | exact resolve eq1657 eq79363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1657
  have eq79545 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq79484
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79484
    | exact resolve eq79484 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq79484
  have eq79600 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq79392
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq79392
    | exact resolve eq79392 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79392
  have eq79604 : x = (M.op y y) := by
    first
    | exact superpose eq79363 eq79545
    | exact resolve eq79545 eq79363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79545
  have eq79624 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq79600 eq27
    | exact resolve eq27 eq79600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq79957 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq16835
       have i₂ := eq79604
       grind)
    | exact superpose eq79604 eq16835
    | exact resolve eq16835 eq79604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16835
  have eq79973 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1 y
       have i₂ := eq79604
       grind)
    | exact superpose eq79604 eq529
    | exact resolve eq529 eq79604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq79977 : ∀ X0 : G, x = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq560 y x
       have i₂ := eq79604
       grind)
    | exact superpose eq79604 eq560
    | exact resolve eq560 eq79604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq79604
  have eq80144 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq79973 x x
       have i₂ := eq1344 x x x
       grind)
    | exact superpose eq1344 eq79973
    | exact resolve eq79973 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344 eq79973
  have eq80154 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq79957
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq79957
    | exact resolve eq79957 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79957
  have eq80172 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq79600 eq80154
    | exact resolve eq80154 eq79600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80154
  have eq84200 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op y (M.op y (M.op x (M.op X0 (M.op X1 x))))) := by
    intro X0 X1
    first
    | exact superpose eq79363 eq5386
    | exact resolve eq5386 eq79363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5386
  have eq84235 : (M.op x (M.op x x)) = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq84200 x x
       have i₂ := eq473 x
       grind)
    | exact superpose eq473 eq84200
    | exact resolve eq84200 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq84200
  have eq84350 : (M.op x (M.op x x)) = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq84235
       have i₂ := eq79429
       grind)
    | exact superpose eq79429 eq84235
    | exact resolve eq84235 eq79429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79429 eq84235
  have eq84375 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq84350
       have i₂ := eq80144
       grind)
    | exact superpose eq80144 eq84350
    | exact resolve eq84350 eq80144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80144 eq84350
  have eq84417 : y ≠ (M.op (M.op x x) y) ∨ (k y y) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq474 (M.op x x) y
       have i₂ := eq84375
       grind)
    | exact superpose eq84375 eq474
    | exact resolve eq474 eq84375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq84375
  have eq84521 : x ≠ y ∨ (k y y) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq84417
       have i₂ := eq79977 x
       grind)
    | exact superpose eq79977 eq84417
    | exact resolve eq84417 eq79977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84417
  have eq84559 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq84521
       have i₂ := eq79977 x
       grind)
    | exact superpose eq79977 eq84521
    | exact resolve eq84521 eq79977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79977 eq84521
  have eq86847 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq80172 eq6312
    | exact resolve eq6312 eq80172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6312
  have eq86938 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq80172 eq1690
    | exact resolve eq1690 eq80172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690 eq80172
  have eq87066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq79624 eq86938
    | exact resolve eq86938 eq79624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86938
  have eq87098 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq86847
    | exact resolve eq86847 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq86847
  have eq87109 : x = y := by
    first
    | (have r₁ := eq87066
       have r₂ := eq28
       grind)
    | exact resolve eq87066 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87066
  have eq87128 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq79363 eq87098
    | exact resolve eq87098 eq79363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79363 eq87098
  have eq87145 : x = (k y y) := by
    first
    | (have r₁ := eq87128
       have r₂ := eq84559
       grind)
    | exact resolve eq87128 eq84559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84559 eq87128
  have eq87157 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq87109
       grind)
    | exact superpose eq87109 eq25
    | exact resolve eq25 eq87109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq87477 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq87157
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq87157
    | exact resolve eq87157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87157
  have eq87552 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq79600 eq87477
    | exact resolve eq87477 eq79600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87477
  have eq88019 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq87552 eq79624
    | exact resolve eq79624 eq87552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79624 eq87552
  have eq88164 : x = (k x x) := by
    first
    | (have i₁ := eq87145
       have i₂ := eq87109
       grind)
    | exact superpose eq87109 eq87145
    | exact resolve eq87145 eq87109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87109 eq87145
  have eq88188 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq742 x x
       have i₂ := eq88164
       grind)
    | exact superpose eq88164 eq742
    | (have j0 := eq742 x x
       grind)
    | exact resolve eq742 eq88164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq88164
  have eq88191 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq88188
  have eq88192 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq88191
  have eq88202 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq88192
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq88192
    | exact resolve eq88192 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq88192
  have eq88221 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq79600 eq88202
    | exact resolve eq88202 eq79600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79600 eq88202
  have eq89879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq88221 eq88019
    | exact resolve eq88019 eq88221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88019 eq88221
  have eq89880 : False := by grind
  exact eq89880

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq19
  have eq43 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq43
    | (have j0 := eq43 (σ X0) (σ X1)
       grind)
    | exact resolve eq43 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq77 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq79 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq78 (σ X0)
       grind)
    | exact superpose eq78 eq31
    | exact resolve eq31 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq149 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq24 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq221 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq16
    | (have j1 := eq56 y x
       grind)
    | exact resolve eq16 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq423 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq221
       have i₂ := eq43 y x
       grind)
    | exact superpose eq43 eq221
    | (have j1 := eq43 (σ y) (σ x)
       grind)
    | exact resolve eq221 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq423
  have eq429 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq426
       grind)
    | exact superpose eq426 eq78
    | exact resolve eq78 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq480 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq221
       have i₂ := eq429
       grind)
    | exact superpose eq429 eq221
    | exact resolve eq221 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq429
  have eq483 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq480
  have eq1278 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq104 X0 X0 (M.op X0 X0) x
       have i₂ := eq149 x X0 X0
       grind)
    | exact superpose eq149 eq104
    | exact resolve eq104 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq149
  have eq4135 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1278 y
       have i₂ := eq426
       grind)
    | exact superpose eq426 eq1278
    | exact resolve eq1278 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq4226 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq483
       have i₂ := eq4135
       grind)
    | exact superpose eq4135 eq483
    | exact resolve eq483 eq4135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq4135
  have eq4253 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4226
  have eq4254 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4253
  have eq4266 : (τ (σ x)) = (k y (τ (σ x))) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq4254
       grind)
    | exact superpose eq4254 eq79
    | exact resolve eq79 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq4289 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1278 (σ y)
       have i₂ := eq4254
       grind)
    | exact superpose eq4254 eq1278
    | exact resolve eq1278 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254
  have eq4324 : x = (k y x) := by
    first
    | (have i₁ := eq4266
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4266
    | exact resolve eq4266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4266
  have eq4502 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4324
       have i₂ := eq43 y x
       grind)
    | exact superpose eq43 eq4324
    | (have j1 := eq43 y x
       grind)
    | exact resolve eq4324 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4324
  have eq4691 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4289
       grind)
    | exact superpose eq4289 eq16
    | exact resolve eq16 eq4289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289
  have eq5231 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4691
       have i₂ := eq4502
       grind)
    | exact superpose eq4502 eq4691
    | exact resolve eq4691 eq4502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4502
  have eq5260 : x = (M.op y y) := by grind
  clear eq5231
  have eq5282 : x = (M.op x y) := by
    first
    | (have i₁ := eq1278 y
       have i₂ := eq5260
       grind)
    | exact superpose eq5260 eq1278
    | exact resolve eq1278 eq5260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278 eq5260
  have eq5311 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4691
       have i₂ := eq5282
       grind)
    | exact superpose eq5282 eq4691
    | exact resolve eq4691 eq5282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4691 eq5282
  have eq5340 : False := by grind
  exact eq5340

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_x_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq51 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq58 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq60 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq81 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq16
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq148 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq207 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq57 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq207 eq57
    | exact resolve eq57 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq343 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq363 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op X1 X0)
       have i₂ := eq60 X1 X0
       grind)
    | exact superpose eq60 eq58
    | exact resolve eq58 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq60 X1 X0
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq59 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq60 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq59 X0 x x X3
       grind)
    | exact superpose eq59 eq60
    | exact resolve eq60 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq468 : (k y (k y y)) = (τ (k (σ y) (k (σ y) (σ y)))) := by
    first
    | exact superpose eq104 eq288
    | exact resolve eq288 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq553 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59 (σ X0) X1 X2 X3
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq59
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq59 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59 X3 X1 X2 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq59
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq59 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq560 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq554 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq561 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq553 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq564 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq566 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq564 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq564
    | (have j0 := eq564 X0
       grind)
    | exact resolve eq564 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq589 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq242 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq242
    | exact resolve eq242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq242 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq242
    | (have j0 := eq242 X0 x
       grind)
    | exact resolve eq242 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq242 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq242
    | (have j0 := eq242 X0 y
       grind)
    | exact resolve eq242 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq242 X1 X0
       have i₂ := eq11 X1 (σ X0)
       grind)
    | exact superpose eq11 eq242
    | (have j1 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1342 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 (M.op X0 X0))
       have i₂ := eq385 X0 X0 X0
       grind)
    | exact superpose eq385 eq57
    | exact resolve eq57 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1343 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq58 (M.op X0 (M.op X0 X0))
       have i₂ := eq385 X0 X0 X0
       grind)
    | exact superpose eq385 eq58
    | exact resolve eq58 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq1611 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq1342 X0
       grind)
    | exact superpose eq1342 eq363
    | exact resolve eq363 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq1638 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1342 eq366
    | exact resolve eq366 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1649 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq366 eq1638
    | exact resolve eq1638 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq1682 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq57 eq1611
    | exact resolve eq1611 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1684 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq212 eq1611
    | exact resolve eq1611 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq1611
  have eq1730 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq1682 X0
       grind)
    | exact superpose eq1682 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq1682 X0
       grind)
    | exact resolve eq13 eq1682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1750 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1781 : (M.op x y) = (k (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq207 eq1750
    | exact resolve eq1750 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1785 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1750 (τ X0)
       grind)
    | exact superpose eq1750 eq35
    | exact resolve eq35 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1786 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq343 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1750 (σ X0)
       grind)
    | exact superpose eq1750 eq343
    | exact resolve eq343 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1788 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1786 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1786
    | exact resolve eq1786 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1789 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1785 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1785
    | exact resolve eq1785 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq2137 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1343 eq366
    | exact resolve eq366 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq2148 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq366 eq2137
    | exact resolve eq2137 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq2137
  have eq6570 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq88 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq88
    | (have j0 := eq88 y
       grind)
    | exact resolve eq88 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq6596 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6570
  have eq6604 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6596
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq6596
    | exact resolve eq6596 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6596
  have eq9002 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq238
    | exact resolve eq238 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq9064 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9002 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq9002
    | (have j0 := eq9002 X0 X1
       grind)
    | exact resolve eq9002 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9002
  have eq11572 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq369 (σ X0) (σ X0) (σ (k X0 X0)) (M.op x x)
       have i₂ := eq561 X0 x x (σ X0)
       grind)
    | exact superpose eq561 eq369
    | (have j1 := eq561 X0 x x x
       grind)
    | exact resolve eq369 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq561
  have eq14147 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op X1 X2) (M.op (σ X0) (σ X0))) (σ (k X0 (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq560 X0 X1 X2 (σ X0)
       have i₂ := eq566 X0
       grind)
    | exact superpose eq566 eq560
    | (have j0 := eq560 X0 X1 X2 x
       have j1 := eq566 X0
       grind)
    | exact resolve eq560 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq566
  have eq14181 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op X1 X2) (M.op (σ X0) (σ X0))) (σ (k X0 (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq14147 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14147
  have eq17482 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17483 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17482
    | exact resolve eq17482 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17482
  have eq17494 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17483
       have r₂ := eq28
       grind)
    | exact resolve eq17483 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17483
  have eq17496 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17494
    | exact resolve eq17494 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17494
  have eq17530 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17496 eq1682
    | exact resolve eq1682 eq17496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17496
  have eq17572 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17530
    | exact resolve eq17530 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17530
  have eq17573 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17572
  have eq17612 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1682 y
       have i₂ := eq17573
       grind)
    | exact superpose eq17573 eq1682
    | exact resolve eq1682 eq17573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17613 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1750 y
       have i₂ := eq17573
       grind)
    | exact superpose eq17573 eq1750
    | exact resolve eq1750 eq17573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17573
  have eq17658 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17613
       have r₂ := eq51
       grind)
    | exact resolve eq17613 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq17613
  have eq17659 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17612
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17612
    | exact resolve eq17612 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17612
  have eq17660 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17659
  have eq17667 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17660 eq28
    | exact resolve eq28 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17669 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17660 eq58
    | exact resolve eq58 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq17698 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17660 eq2148
    | exact resolve eq2148 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq17702 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17698
    | exact resolve eq17698 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17698
  have eq17819 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq17658
       grind)
    | exact superpose eq17658 eq85
    | exact resolve eq85 eq17658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17658
  have eq17838 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17819
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17819
    | exact resolve eq17819 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17819
  have eq17843 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq17838
       have r₂ := eq52
       grind)
    | exact resolve eq17838 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq17838
  have eq17856 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq98 eq17843
    | exact resolve eq17843 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq17860 : (τ (σ y)) = (k y x) := by
    first
    | exact superpose eq17843 eq95
    | exact resolve eq95 eq17843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq17878 : y = (k y x) := by
    first
    | exact superpose eq30 eq17860
    | exact resolve eq17860 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17860
  have eq19615 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1682 y
       have i₂ := eq17856
       grind)
    | exact superpose eq17856 eq1682
    | exact resolve eq1682 eq17856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17856
  have eq19661 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq19615
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19615
    | exact resolve eq19615 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19615
  have eq19662 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq19661
  have eq19672 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19662 eq30
    | exact resolve eq30 eq19662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19843 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq19672
    | exact resolve eq19672 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19672
  have eq19944 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq25986 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17702 eq17669
    | exact resolve eq17669 eq17702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17669 eq17702
  have eq26028 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq25986
  have eq26064 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17660 eq26028
    | exact resolve eq26028 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17660 eq26028
  have eq26100 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq26064
  have eq26119 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26100 eq59
    | exact resolve eq59 eq26100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq26100
  have eq26166 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26119 x x
       have i₂ := eq414 sF3 (M.op x x)
       grind)
    | exact superpose eq414 eq26119
    | exact resolve eq26119 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26119
  have eq249282 : (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17843 eq9064
    | (have j0 := eq9064 (σ y) (σ x)
       grind)
    | exact resolve eq9064 eq17843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9064
  have eq250053 : (σ (M.op (σ x) (σ y))) = (σ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq249282
    | exact resolve eq249282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249282
  have eq250167 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op (σ x) (σ y))) = (σ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq250053
    | exact resolve eq250053 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250053
  have eq363823 : (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) = (M.op (σ (k (k y x) (k y x))) (k (σ y) (σ x))) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq11572 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq11572
    | exact resolve eq11572 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11572
  have eq364038 : (M.op (σ y) (σ y)) = (M.op (σ (k (k y x) (k y x))) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | exact superpose eq17843 eq363823
    | exact resolve eq363823 eq17843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363823
  have eq364183 : (M.op (σ y) (σ y)) = (M.op (σ (k y y)) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq364038
       have i₂ := eq17878
       grind)
    | exact superpose eq17878 eq364038
    | exact resolve eq364038 eq17878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364038
  have eq364311 : (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq364183
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq364183
    | exact resolve eq364183 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364183
  have eq364330 : (M.op (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq17843 eq364311
    | exact resolve eq364311 eq17843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364311
  have eq375505 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (M.op (k (σ y) (σ x)) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq611 (k y x) x
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq611
    | exact resolve eq611 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq611
  have eq375868 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq17843 eq375505
    | (have j0 := eq375505 X0
       grind)
    | exact resolve eq375505 eq17843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375505
  have eq375922 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq375868 X0
       have i₂ := eq17878
       grind)
    | exact superpose eq17878 eq375868
    | (have j0 := eq375868 X0
       grind)
    | exact resolve eq375868 eq17878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375868
  have eq375936 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (M.op (σ y) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq375922 X0
       have i₂ := eq605 X0
       grind)
    | exact superpose eq605 eq375922
    | (have j0 := eq375922 X0
       grind)
    | exact resolve eq375922 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq375922
  have eq375947 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (τ (k X0 (σ y))) = (τ (M.op (σ y) X0)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq17843 eq375936
    | (have j0 := eq375936 X0
       grind)
    | exact resolve eq375936 eq17843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375936
  have eq375954 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (M.op (σ y) X0)) ∨ (M.op X0 X0) = (σ y) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq17843 eq375947
    | (have j0 := eq375947 X0
       grind)
    | exact resolve eq375947 eq17843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17843 eq375947
  have eq513285 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op (σ x) (σ y))) = (σ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq250167 eq1682
    | exact resolve eq1682 eq250167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682 eq250167
  have eq513570 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op (σ x) (σ y))) = (σ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq513285
    | exact resolve eq513285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513285
  have eq513571 : (σ (M.op (σ x) (σ y))) = (σ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq513570
  have eq513649 : ∀ X0 : G, (τ (k (σ (σ y)) X0)) = (k (M.op (σ x) (σ y)) (τ X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq513571 eq343
    | exact resolve eq343 eq513571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513670 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (τ (M.op (σ (σ y)) (σ (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq513571 eq1788
    | exact resolve eq1788 eq513571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513571
  have eq513801 : ∀ X0 : G, (k (σ y) (τ X0)) = (k (M.op (σ x) (σ y)) (τ X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq513649 x
       have i₂ := eq343 sF3 x
       grind)
    | exact superpose eq343 eq513649
    | exact resolve eq513649 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq513649
  have eq513845 : ∀ X0 : G, (k (σ y) X0) = (k (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq513801 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq513801
    | exact resolve eq513801 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513801
  have eq514221 : ∀ X0 : G, (τ (k (σ y) (σ X0))) = (k (τ (M.op (σ x) (σ y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq513845 eq242
    | exact resolve eq242 eq513845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513845
  have eq514461 : ∀ X0 : G, (k (τ (σ y)) X0) = (k (τ (M.op (σ x) (σ y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq514221 x
       have i₂ := eq242 sF3 x
       grind)
    | exact superpose eq242 eq514221
    | exact resolve eq514221 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq514221
  have eq514497 : ∀ X0 : G, (k y X0) = (k (τ (M.op (σ x) (σ y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq514461
    | exact resolve eq514461 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514461
  have eq514740 : ∀ X0 : G, (k y (τ X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq514497 eq589
    | exact resolve eq589 eq514497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq514854 : (k y x) = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq514497 eq604
    | exact resolve eq604 eq514497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq514497
  have eq514875 : y = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq514854
       have i₂ := eq17878
       grind)
    | exact superpose eq17878 eq514854
    | exact resolve eq514854 eq17878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17878 eq514854
  have eq514966 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq514740 X0
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq514740
    | exact resolve eq514740 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq514740
  have eq515316 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq514875 eq15
    | exact resolve eq15 eq514875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514875
  have eq515591 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq515316
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq515316
    | exact resolve eq515316 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515316
  have eq546983 : (τ (M.op (σ x) (σ y))) = (τ (k (σ y) (τ (M.op (σ (σ y)) (σ (σ y)))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq513670 eq514966
    | exact resolve eq514966 eq513670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513670 eq514966
  have eq546992 : (τ (M.op (σ x) (σ y))) = (τ (k (σ y) (τ (M.op (σ (σ y)) (σ (σ y)))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq546983
  have eq547005 : (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq546992
       have i₂ := eq1788 sF3
       grind)
    | exact superpose eq1788 eq546992
    | exact resolve eq546992 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788 eq546992
  have eq547016 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq547005
    | exact resolve eq547005 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547005
  have eq547076 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq547016 eq1789
    | exact resolve eq1789 eq547016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq547016
  have eq670552 : (k (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq364330 eq13
    | (have j0 := eq13 (σ y) (k (σ y) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq364330
       grind)
    | exact resolve eq13 eq364330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364330
  have eq670748 : (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq670552
       have r₂ := eq6604
       grind)
    | exact resolve eq670552 eq6604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6604 eq670552
  have eq670762 : (τ (σ y)) = (k y (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq670748 eq468
    | exact resolve eq468 eq670748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq670748
  have eq670780 : y = (k y (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq670762
    | exact resolve eq670762 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq670762
  have eq1527621 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (k y y)) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14181 y X0 X1
       have i₂ := eq670780
       grind)
    | exact superpose eq670780 eq14181
    | (have j0 := eq14181 y X1 x
       grind)
    | exact resolve eq14181 eq670780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14181 eq670780
  have eq1528105 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (k y y)) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1527621 x x
       have i₂ := eq414 (σ y) (M.op x x)
       grind)
    | exact superpose eq414 eq1527621
    | exact resolve eq1527621 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq1527621
  have eq1528106 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (k y y)) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1528105
  have eq1528387 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (k y y)) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1528106
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1528106
    | exact resolve eq1528106 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528106
  have eq1528388 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (k y y)) = (M.op (σ (k y y)) (σ y)) := by grind
  clear eq1528387
  have eq1528649 : (σ (k y y)) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1528388
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1528388
    | exact resolve eq1528388 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528388
  have eq1528705 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1528649
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq1528649
    | exact resolve eq1528649 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528649
  have eq2803042 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq375954 eq104
    | (have j1 := eq375954 (σ y)
       grind)
    | exact resolve eq104 eq375954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq375954
  have eq2803596 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2803042
  have eq2840007 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26166 eq2803596
    | exact resolve eq2803596 eq26166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26166 eq2803596
  have eq2840620 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2840007
    | exact resolve eq2840007 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840007
  have eq2840626 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq2840620
       grind)
    | exact superpose eq2840620 eq86
    | exact resolve eq86 eq2840620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2840620
  have eq2841123 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2840626
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2840626
    | exact resolve eq2840626 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840626
  have eq2841663 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19662 eq2841123
    | exact resolve eq2841123 eq19662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19662 eq2841123
  have eq2841983 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2841663
  have eq2842070 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2841983
       have r₂ := eq17667
       grind)
    | exact resolve eq2841983 eq17667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17667 eq2841983
  have eq2842098 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2842070 eq148
    | exact resolve eq148 eq2842070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq2842070
  have eq2842355 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2842098
    | exact resolve eq2842098 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2842098
  have eq2842580 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2842355 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq2842355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2842665 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2842580
  have eq2842740 : x = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq207 eq2842665
    | exact resolve eq2842665 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842665
  have eq2842966 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq207 eq2842740
    | exact resolve eq2842740 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq2842740
  have eq3643889 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2842966 eq1781
    | exact resolve eq1781 eq2842966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781 eq2842966
  have eq3668157 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3643889 eq2842355
    | exact resolve eq2842355 eq3643889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842355 eq3643889
  have eq3668471 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3668157
  have eq3668938 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3668471 eq1684
    | exact resolve eq1684 eq3668471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684 eq3668471
  have eq3669725 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq19843 eq3668938
    | exact resolve eq3668938 eq19843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19843 eq3668938
  have eq3670306 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3669725
       have r₂ := eq19944
       grind)
    | exact resolve eq3669725 eq19944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19944 eq3669725
  have eq3670351 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3670306
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3670306
    | exact resolve eq3670306 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670306
  have eq3670352 : x = (M.op x y) := by grind
  clear eq3670351
  have eq3670368 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3670352 eq21
    | exact resolve eq21 eq3670352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3670478 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq3670352 eq1649
    | exact resolve eq1649 eq3670352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq3671403 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3670478
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3670478
    | exact resolve eq3670478 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3670478
  have eq3671470 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3670368
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3670368
    | exact resolve eq3670368 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670368
  have eq3671526 : x = (M.op y y) := by
    first
    | exact superpose eq3670352 eq3671403
    | exact resolve eq3671403 eq3670352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670352 eq3671403
  have eq3671556 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3671470 eq27
    | exact resolve eq27 eq3671470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3672394 : (σ y) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3671470 eq515591
    | exact resolve eq515591 eq3671470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515591
  have eq3673126 : (σ y) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3672394
       have r₂ := eq28
       grind)
    | exact resolve eq3672394 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672394
  have eq3673235 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq3671526
       grind)
    | exact superpose eq3671526 eq105
    | exact resolve eq105 eq3671526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq3673253 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq547076
       have i₂ := eq3671526
       grind)
    | exact superpose eq3671526 eq547076
    | exact resolve eq547076 eq3671526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547076 eq3671526
  have eq3674411 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3673253
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3673253
    | exact resolve eq3673253 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673253
  have eq3674419 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3673235
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3673235
    | exact resolve eq3673235 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673235
  have eq3674558 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3671470 eq3674411
    | exact resolve eq3674411 eq3671470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674411
  have eq3674562 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3671470 eq3674419
    | exact resolve eq3674419 eq3671470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674419
  have eq3674616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3671470 eq3674558
    | exact resolve eq3674558 eq3671470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674558
  have eq3674632 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3674616
       have r₂ := eq28
       grind)
    | exact resolve eq3674616 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674616
  have eq3675784 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3673126 eq3674632
    | exact resolve eq3674632 eq3673126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673126 eq3674632
  have eq3675786 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq3675784 eq28
    | exact resolve eq28 eq3675784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675784
  have eq3739811 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3674562 eq1528705
    | exact resolve eq1528705 eq3674562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528705
  have eq3740200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3671556 eq3739811
    | exact resolve eq3739811 eq3671556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671556 eq3739811
  have eq3740279 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq3740200
       have r₂ := eq28
       grind)
    | exact resolve eq3740200 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3740200
  have eq3740557 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3740279 eq1750
    | exact resolve eq1750 eq3740279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750 eq3740279
  have eq3743516 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3740557 eq3674562
    | exact resolve eq3674562 eq3740557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674562 eq3740557
  have eq3743776 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq3743516
  have eq3743858 : x = y := by
    first
    | (have r₁ := eq3743776
       have r₂ := eq3675786
       grind)
    | exact resolve eq3743776 eq3675786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3743776
  have eq3743922 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3743858
       grind)
    | exact superpose eq3743858 eq25
    | exact resolve eq25 eq3743858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3743858
  have eq3746155 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3743922
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3743922
    | exact resolve eq3743922 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3743922
  have eq3746499 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3671470 eq3746155
    | exact resolve eq3746155 eq3671470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671470 eq3746155
  have eq3746611 : False := by grind
  exact eq3746611
