import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_x_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq100 : ∀ X0 : G, (M.op X0 (k X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq153 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq245 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq248 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq294 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
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
  have eq349 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq371 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq375 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
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
  have eq396 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  have eq430 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq541 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq248
    | exact resolve eq248 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq248 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq248
    | (have j0 := eq248 X0 x
       grind)
    | exact resolve eq248 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq248 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq248
    | (have j0 := eq248 X0 y
       grind)
    | exact resolve eq248 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X1 X0
       have i₂ := eq11 X1 (σ X0)
       grind)
    | exact superpose eq11 eq248
    | (have j1 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (k (σ X0) (σ (k X0 X0)))) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq100 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq100
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq100 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq100
  have eq826 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (k (σ X0) (σ (k X0 X0)))) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq809 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq836 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq826 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq826
    | (have j0 := eq826 X0
       grind)
    | exact resolve eq826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq1665 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 (M.op X0 X0))
       have i₂ := eq396 X0 X0 X0
       grind)
    | exact superpose eq396 eq57
    | exact resolve eq57 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1666 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq58 (M.op X0 (M.op X0 X0))
       have i₂ := eq396 X0 X0 X0
       grind)
    | exact superpose eq396 eq58
    | exact resolve eq58 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq1844 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq1665 X0
       grind)
    | exact superpose eq1665 eq371
    | exact resolve eq371 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq1873 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1665 eq375
    | exact resolve eq375 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq1885 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq375 eq1873
    | exact resolve eq1873 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq1922 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq57 eq1844
    | exact resolve eq1844 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1844
  have eq1977 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq1922 X0
       grind)
    | exact superpose eq1922 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq1922 X0
       grind)
    | exact resolve eq13 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1998 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1977 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq2038 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq1998 (τ X0)
       grind)
    | exact superpose eq1998 eq35
    | exact resolve eq35 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2039 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq349 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq1998 (σ X0)
       grind)
    | exact superpose eq1998 eq349
    | exact resolve eq349 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2041 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2039 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq2039
    | exact resolve eq2039 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq2042 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2038 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2038
    | exact resolve eq2038 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq2239 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1666 eq375
    | exact resolve eq375 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666
  have eq2251 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq375 eq2239
    | exact resolve eq2239 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq2239
  have eq10238 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq245
    | exact resolve eq245 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq10325 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10238 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq10238
    | (have j0 := eq10238 X0 X1
       grind)
    | exact resolve eq10238 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10238
  have eq15235 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq836 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq836
    | (have j0 := eq836 X0
       have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15248 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 (σ (k (τ X0) (k (τ X0) (τ X0))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq836 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq836
    | exact resolve eq836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq15369 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15235 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15235
  have eq15383 : ∀ X0 : G, (k X0 (σ (τ X0))) = (M.op (k X0 (σ (τ X0))) X0) ∨ (M.op X0 (σ (k (τ X0) (k (τ X0) (τ X0))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15248 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq15248
    | (have j0 := eq15248 X0
       grind)
    | exact resolve eq15248 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15248
  have eq15397 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15369 X0
       have i₂ := eq1998 X0
       grind)
    | exact superpose eq1998 eq15369
    | (have j0 := eq15369 X0
       grind)
    | exact resolve eq15369 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15369
  have eq15398 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15397 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15397
  have eq15405 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 (σ (k (τ X0) (k (τ X0) (τ X0))))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15383 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15383
    | (have j0 := eq15383 X0
       grind)
    | exact resolve eq15383 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383
  have eq15415 : ∀ X0 : G, (M.op X0 (k X0 (σ (k (τ X0) (τ X0))))) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15405 X0
       have i₂ := eq35 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq35 eq15405
    | (have j0 := eq15405 X0
       grind)
    | exact resolve eq15405 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15405
  have eq15425 : ∀ X0 : G, (M.op X0 (k X0 (k X0 (σ (τ X0))))) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15415 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq15415
    | (have j0 := eq15415 X0
       grind)
    | exact resolve eq15415 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq15415
  have eq15435 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 (k X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15425 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15425
    | (have j0 := eq15425 X0
       grind)
    | exact resolve eq15425 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15425
  have eq17969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17969
    | exact resolve eq17969 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17969
  have eq17981 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17970
       have r₂ := eq28
       grind)
    | exact resolve eq17970 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17970
  have eq17983 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17981
    | exact resolve eq17981 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17981
  have eq18024 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17983 eq1922
    | exact resolve eq1922 eq17983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17983
  have eq18068 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18024
    | exact resolve eq18024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18024
  have eq18069 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18068
  have eq18654 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1922 y
       have i₂ := eq18069
       grind)
    | exact superpose eq18069 eq1922
    | exact resolve eq1922 eq18069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18655 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1998 y
       have i₂ := eq18069
       grind)
    | exact superpose eq18069 eq1998
    | exact resolve eq1998 eq18069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18069
  have eq18705 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18655
       have r₂ := eq51
       grind)
    | exact resolve eq18655 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq18655
  have eq18706 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18654
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18654
    | exact resolve eq18654 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18654
  have eq18707 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18706
  have eq18724 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18707 eq28
    | exact resolve eq28 eq18707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18726 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18707 eq58
    | exact resolve eq58 eq18707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq18755 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18707 eq2251
    | exact resolve eq2251 eq18707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq18759 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18755
    | exact resolve eq18755 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18755
  have eq18922 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18705
       grind)
    | exact superpose eq18705 eq85
    | exact resolve eq85 eq18705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18705
  have eq18941 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18922
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18922
    | exact resolve eq18922 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18922
  have eq18946 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq18941
       have r₂ := eq52
       grind)
    | exact resolve eq18941 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq18941
  have eq18959 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq98 eq18946
    | exact resolve eq18946 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq18963 : (τ (σ y)) = (k y x) := by
    first
    | exact superpose eq18946 eq95
    | exact resolve eq95 eq18946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq18981 : y = (k y x) := by
    first
    | exact superpose eq30 eq18963
    | exact resolve eq18963 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18963
  have eq21492 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1922 y
       have i₂ := eq18959
       grind)
    | exact superpose eq18959 eq1922
    | exact resolve eq1922 eq18959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18959
  have eq21544 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq21492
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21492
    | exact resolve eq21492 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21492
  have eq21545 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq21544
  have eq21570 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21545 eq30
    | exact resolve eq30 eq21545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21582 : (k y y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21545 eq109
    | exact resolve eq109 eq21545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21724 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq153 eq21582
    | exact resolve eq21582 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21582
  have eq21733 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq21570
    | exact resolve eq21570 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq21570
  have eq21836 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq21733
  have eq28077 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18759 eq18726
    | exact resolve eq18726 eq18759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18726 eq18759
  have eq28127 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq28077
  have eq28181 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18707 eq28127
    | exact resolve eq28127 eq18707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18707 eq28127
  have eq28225 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq28181
  have eq28243 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28225 eq59
    | exact resolve eq59 eq28225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq28225
  have eq28297 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28243 x x
       have i₂ := eq430 sF3 (M.op x x)
       grind)
    | exact superpose eq430 eq28243
    | exact resolve eq28243 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq28243
  have eq266691 : (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18946 eq10325
    | (have j0 := eq10325 (σ y) (σ x)
       grind)
    | exact resolve eq10325 eq18946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10325
  have eq267471 : (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq266691
    | exact resolve eq266691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266691
  have eq267590 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq267471
    | exact resolve eq267471 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267471
  have eq405895 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (M.op (k (σ y) (σ x)) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq563 (k y x) x
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq563
    | exact resolve eq563 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq406270 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (M.op (σ y) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq18946 eq405895
    | (have j0 := eq405895 X0
       grind)
    | exact resolve eq405895 eq18946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405895
  have eq406329 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq406270 X0
       have i₂ := eq18981
       grind)
    | exact superpose eq18981 eq406270
    | (have j0 := eq406270 X0
       grind)
    | exact resolve eq406270 eq18981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406270
  have eq406341 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (M.op (σ y) X0)) ∨ (M.op X0 X0) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq406329 X0
       have i₂ := eq557 X0
       grind)
    | exact superpose eq557 eq406329
    | (have j0 := eq406329 X0
       grind)
    | exact resolve eq406329 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq406329
  have eq406352 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (τ (k X0 (σ y))) = (τ (M.op (σ y) X0)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq18946 eq406341
    | (have j0 := eq406341 X0
       grind)
    | exact resolve eq406341 eq18946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406341
  have eq406359 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (M.op (σ y) X0)) ∨ (M.op X0 X0) = (σ y) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq18946 eq406352
    | (have j0 := eq406352 X0
       grind)
    | exact resolve eq406352 eq18946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406352
  have eq567006 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq267590 eq1922
    | exact resolve eq1922 eq267590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922 eq267590
  have eq567304 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq567006
    | exact resolve eq567006 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567006
  have eq567305 : (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq567304
  have eq567393 : ∀ X0 : G, (τ (k (σ (σ y)) X0)) = (k (M.op (σ x) (σ y)) (τ X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq567305 eq349
    | exact resolve eq349 eq567305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567414 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (τ (M.op (σ (σ y)) (σ (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq567305 eq2041
    | exact resolve eq2041 eq567305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567305
  have eq567545 : ∀ X0 : G, (k (σ y) (τ X0)) = (k (M.op (σ x) (σ y)) (τ X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq567393 x
       have i₂ := eq349 sF3 x
       grind)
    | exact superpose eq349 eq567393
    | exact resolve eq567393 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq567393
  have eq568377 : ∀ X0 : G, (k (σ y) X0) = (k (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq567545 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq567545
    | exact resolve eq567545 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567545
  have eq568798 : ∀ X0 : G, (τ (k (σ y) (σ X0))) = (k (τ (M.op (σ x) (σ y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq568377 eq248
    | exact resolve eq248 eq568377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568377
  have eq569079 : ∀ X0 : G, (k (τ (σ y)) X0) = (k (τ (M.op (σ x) (σ y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq568798 x
       have i₂ := eq248 sF3 x
       grind)
    | exact superpose eq248 eq568798
    | exact resolve eq568798 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq568798
  have eq569117 : ∀ X0 : G, (k y X0) = (k (τ (M.op (σ x) (σ y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq569079
    | exact resolve eq569079 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569079
  have eq571758 : ∀ X0 : G, (k y (τ X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq569117 eq541
    | exact resolve eq541 eq569117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq571897 : (k y x) = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq569117 eq556
    | exact resolve eq556 eq569117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq569117
  have eq571918 : y = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq571897
       have i₂ := eq18981
       grind)
    | exact superpose eq18981 eq571897
    | exact resolve eq571897 eq18981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571897
  have eq572034 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq571758 X0
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq571758
    | exact resolve eq571758 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq571758
  have eq573318 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq571918 eq15
    | exact resolve eq15 eq571918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571918
  have eq573625 : (σ y) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq573318
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq573318
    | exact resolve eq573318 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573318
  have eq595180 : (τ (M.op (σ x) (σ y))) = (τ (k (σ y) (τ (M.op (σ (σ y)) (σ (σ y)))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq567414 eq572034
    | exact resolve eq572034 eq567414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567414 eq572034
  have eq595189 : (τ (M.op (σ x) (σ y))) = (τ (k (σ y) (τ (M.op (σ (σ y)) (σ (σ y)))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq595180
  have eq595202 : (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq595189
       have i₂ := eq2041 sF3
       grind)
    | exact superpose eq2041 eq595189
    | exact resolve eq595189 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041 eq595189
  have eq595213 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq595202
    | exact resolve eq595202 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595202
  have eq595273 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq595213 eq2042
    | exact resolve eq2042 eq595213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042 eq595213
  have eq681407 : (σ (M.op (k y x) (k y x))) = (M.op (σ (M.op (k y x) (k y x))) (k (σ y) (σ x))) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (k y x) = (M.op (k y x) (k y x)) := by
    first
    | (have i₁ := eq15398 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq15398
    | (have j0 := eq15398 (k (σ y) (σ x))
       grind)
    | exact resolve eq15398 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq15398
  have eq681746 : (σ (M.op (k y x) (k y x))) = (M.op (σ (M.op (k y x) (k y x))) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (k y x) = (M.op (k y x) (k y x)) := by
    first
    | exact superpose eq18946 eq681407
    | exact resolve eq681407 eq18946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681407
  have eq681976 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (k y x) = (M.op (k y x) (k y x)) := by
    first
    | (have i₁ := eq681746
       have i₂ := eq18981
       grind)
    | exact superpose eq18981 eq681746
    | exact resolve eq681746 eq18981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681746
  have eq682188 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (k y x) = (M.op (k y x) (k y x)) := by
    first
    | exact superpose eq18946 eq681976
    | exact resolve eq681976 eq18946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18946 eq681976
  have eq682367 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq682188
       have i₂ := eq18981
       grind)
    | exact superpose eq18981 eq682188
    | exact resolve eq682188 eq18981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682188
  have eq4146013 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq406359 eq109
    | (have j1 := eq406359 (σ y)
       grind)
    | exact resolve eq109 eq406359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406359
  have eq4146592 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4146013
  have eq4147062 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28297 eq4146592
    | exact resolve eq4146592 eq28297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28297 eq4146592
  have eq4147700 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4147062
    | exact resolve eq4147062 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147062
  have eq4147704 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq4147700
       grind)
    | exact superpose eq4147700 eq86
    | exact resolve eq86 eq4147700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq4147700
  have eq4148612 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4147704
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4147704
    | exact resolve eq4147704 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147704
  have eq4150318 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21545 eq4148612
    | exact resolve eq4148612 eq21545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21545 eq4148612
  have eq4150861 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq4150318
  have eq4151089 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4150861
       have r₂ := eq18724
       grind)
    | exact resolve eq4150861 eq18724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18724 eq4150861
  have eq4151232 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4151089 eq153
    | exact resolve eq153 eq4151089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq4151089
  have eq4151700 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4151232
    | exact resolve eq4151232 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4151232
  have eq4151755 : x = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4151700 eq21724
    | exact resolve eq21724 eq4151700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21724 eq4151700
  have eq4152228 : x = (k y y) ∨ x = (M.op x y) := by grind
  clear eq4151755
  have eq4156463 : x = (M.op x y) ∨ y = (M.op y (k y x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15435 y
       have i₂ := eq4152228
       grind)
    | exact superpose eq4152228 eq15435
    | (have j0 := eq15435 y
       grind)
    | exact resolve eq15435 eq4152228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15435
  have eq4157016 : x = (M.op x y) ∨ y = (M.op y (k y x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4156463
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4156463
    | exact resolve eq4156463 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4156463
  have eq4157017 : x = (M.op x y) ∨ y = (M.op y (k y x)) ∨ y = (M.op y y) := by grind
  clear eq4157016
  have eq4157441 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4157017
       have i₂ := eq18981
       grind)
    | exact superpose eq18981 eq4157017
    | exact resolve eq4157017 eq18981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18981 eq4157017
  have eq4157442 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq4157441
  have eq4168371 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1998 y
       have i₂ := eq4157442
       grind)
    | exact superpose eq4157442 eq1998
    | exact resolve eq1998 eq4157442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998 eq4157442
  have eq4171295 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4152228
       have i₂ := eq4168371
       grind)
    | exact superpose eq4168371 eq4152228
    | exact resolve eq4152228 eq4168371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4152228 eq4168371
  have eq4171912 : x = y ∨ x = (M.op x y) := by grind
  clear eq4171295
  have eq4172111 : x = (M.op x y) := by
    first
    | (have r₁ := eq4171912
       have r₂ := eq21836
       grind)
    | exact resolve eq4171912 eq21836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21836 eq4171912
  have eq4172504 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4172111 eq21
    | exact resolve eq21 eq4172111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq4172615 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq4172111 eq1885
    | exact resolve eq1885 eq4172111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq4173223 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4172615
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq4172615
    | exact resolve eq4172615 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4172615
  have eq4173290 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4172504
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4172504
    | exact resolve eq4172504 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172504
  have eq4173314 : x = (M.op y y) := by
    first
    | exact superpose eq4172111 eq4173223
    | exact resolve eq4173223 eq4172111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172111 eq4173223
  have eq4174310 : (σ y) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4173290 eq573625
    | exact resolve eq573625 eq4173290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573625
  have eq4175127 : (σ y) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq4174310
       have r₂ := eq28
       grind)
    | exact resolve eq4174310 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4174310
  have eq4175254 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq595273
       have i₂ := eq4173314
       grind)
    | exact superpose eq4173314 eq595273
    | exact resolve eq595273 eq4173314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595273
  have eq4176601 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4175254
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4175254
    | exact resolve eq4175254 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4175254
  have eq4176779 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4173290 eq4176601
    | exact resolve eq4176601 eq4173290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176601
  have eq4176851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4173290 eq4176779
    | exact resolve eq4176779 eq4173290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176779
  have eq4176874 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq4176851
       have r₂ := eq28
       grind)
    | exact resolve eq4176851 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176851
  have eq4178114 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4175127 eq4176874
    | exact resolve eq4176874 eq4175127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4175127 eq4176874
  have eq4178116 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq4178114 eq28
    | exact resolve eq28 eq4178114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4201804 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq682367
       have i₂ := eq4173314
       grind)
    | exact superpose eq4173314 eq682367
    | exact resolve eq682367 eq4173314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682367
  have eq4201805 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4201804
       have i₂ := eq4173314
       grind)
    | exact superpose eq4173314 eq4201804
    | exact resolve eq4201804 eq4173314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4201804
  have eq4201806 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4201805
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4201805
    | exact resolve eq4201805 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4201805
  have eq4201807 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq4201806
    | exact resolve eq4201806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4201806
  have eq4201808 : (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4178114 eq4201807
    | exact resolve eq4201807 eq4178114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4178114 eq4201807
  have eq4201809 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4173290 eq4201808
    | exact resolve eq4201808 eq4173290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4201808
  have eq4201810 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq4201809
       have r₂ := eq4178116
       grind)
    | exact resolve eq4201809 eq4178116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4201809
  have eq4202361 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4201810 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq4201810
       grind)
    | exact resolve eq13 eq4201810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4201810
  have eq4202822 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq4202361
  have eq4203593 : (τ (σ y)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq4202822 eq109
    | exact resolve eq109 eq4202822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq4202822
  have eq4204367 : y = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq4203593
    | exact resolve eq4203593 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4203593
  have eq4204813 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq4204367
       grind)
    | exact superpose eq4204367 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq4204367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204367
  have eq4204910 : y = (M.op y y) ∨ x = y := by grind
  clear eq4204813
  have eq4205111 : x = y ∨ x = y := by
    first
    | (have i₁ := eq4204910
       have i₂ := eq4173314
       grind)
    | exact superpose eq4173314 eq4204910
    | exact resolve eq4204910 eq4173314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4173314 eq4204910
  have eq4205112 : x = y := by grind
  clear eq4205111
  have eq4205790 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq4205112
       grind)
    | exact superpose eq4205112 eq25
    | exact resolve eq25 eq4205112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4205112
  have eq4207515 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4205790
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4205790
    | exact resolve eq4205790 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq4205790
  have eq4207769 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4173290 eq4207515
    | exact resolve eq4207515 eq4173290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4173290 eq4207515
  have eq4207872 : False := by grind
  exact eq4207872

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_x_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq80 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq96 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq82 eq16
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq146 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq189 : (σ (k (k y x) (M.op x y))) = (k (k (σ y) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (k y x)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq41
    | exact resolve eq41 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq200 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq56 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : (M.op y (M.op x y)) ≠ (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq200 eq12
    | exact resolve eq12 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq200 eq56
    | exact resolve eq56 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (k (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by grind
  clear eq204
  have eq357 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq81
    | (have j1 := eq98 y
       grind)
    | exact resolve eq81 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq98
  have eq378 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq56 eq59
    | exact resolve eq59 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq390 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X1 X0)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq57
    | exact resolve eq57 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  have eq443 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 (M.op X1 X0))) (M.op (M.op X1 X0) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 (M.op X1 X0) X2 X3 X4
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq465 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
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
  have eq466 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
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
  clear eq58
  have eq471 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq466
    | exact resolve eq466 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq472 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq465 X0 X1 X2 X3
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq465
    | exact resolve eq465 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq736 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq378 eq14
    | exact resolve eq14 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq743 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq736 X0
       have i₂ := eq59 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq59 eq736
    | exact resolve eq736 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq746 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq743 X0
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq743
    | exact resolve eq743 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq743
  have eq803 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq67 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq67 X0 X0
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq67 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq67 X0 X0
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq823 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq808 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq824 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq823 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq825 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq803 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq826 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq824
    | (have j0 := eq824 X0 X1
       grind)
    | exact resolve eq824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq829 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1466 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq429 X0 X0 X0
       grind)
    | exact superpose eq429 eq14
    | exact resolve eq14 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1467 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op X0 X0))
       have i₂ := eq429 X0 X0 X0
       grind)
    | exact superpose eq429 eq56
    | exact resolve eq56 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1468 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 (M.op X0 X0))
       have i₂ := eq429 X0 X0 X0
       grind)
    | exact superpose eq429 eq57
    | exact resolve eq57 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1479 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq460 (M.op x (M.op x x)) x
       have i₂ := eq429 x x x
       grind)
    | exact superpose eq429 eq460
    | exact resolve eq460 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1697 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq746 X0
       have i₂ := eq1467 X0
       grind)
    | exact superpose eq1467 eq746
    | exact resolve eq746 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq1698 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq386 X0
       have i₂ := eq1467 X0
       grind)
    | exact superpose eq1467 eq386
    | exact resolve eq386 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq1726 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1467 eq390
    | exact resolve eq390 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1737 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq390 eq1726
    | exact resolve eq1726 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1770 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq56 eq1698
    | exact resolve eq1698 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1772 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq207 eq1698
    | exact resolve eq1698 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq1698
  have eq1819 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq1770 X0
       grind)
    | exact superpose eq1770 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq1770 X0
       grind)
    | exact resolve eq13 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1839 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq1869 : (M.op x y) = (k (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq200 eq1839
    | exact resolve eq1839 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq2126 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1468 eq390
    | exact resolve eq390 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq2137 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq390 eq2126
    | exact resolve eq2126 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq2126
  have eq2515 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1479 X0 X1
       have i₂ := eq1467 X0
       grind)
    | exact superpose eq1467 eq1479
    | exact resolve eq1479 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq1479
  have eq5965 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq472 X0 X1 X2 X3
       have i₂ := eq471 X0 X1
       grind)
    | exact superpose eq471 eq472
    | exact resolve eq472 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq6199 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5965 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq429 x X1 X0
       grind)
    | exact superpose eq429 eq5965
    | exact resolve eq5965 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq6210 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op X2 X1) (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5965 (M.op X2 X1) (M.op X0 X0) (M.op X1 (M.op X2 X1)) (M.op x x)
       have i₂ := eq443 X1 X2 x x X0
       grind)
    | exact superpose eq443 eq5965
    | exact resolve eq5965 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq6249 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)))) = (M.op (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq471 (M.op X2 (M.op X0 X1)) (M.op X0 X1)
       have i₂ := eq5965 X0 X1 (M.op X0 X1) X2
       grind)
    | exact superpose eq5965 eq471
    | exact resolve eq471 eq5965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq5965
  have eq6316 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2515 eq6249
    | exact resolve eq6249 eq2515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515 eq6249
  have eq12295 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq826 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq15678 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq829 X0 X1
       have j1 := eq821 X0 X1
       grind)
    | (have r₁ := eq829 X0 X1
       have r₂ := eq821 X0 X1
       grind)
    | (have r₁ := eq829 X1 X1
       have r₂ := eq821 X1 X1
       grind)
    | exact resolve eq829 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq829
  have eq15679 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq15678 X0 X1
       have j1 := eq822 X0 X1
       grind)
    | (have r₁ := eq15678 X0 X1
       have r₂ := eq822 X0 X1
       grind)
    | (have r₁ := eq15678 X0 X0
       have r₂ := eq822 X0 X1
       grind)
    | exact resolve eq15678 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq15678
  have eq15771 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15679
    | (have j0 := eq15679 (M.op x y) X0
       grind)
    | exact resolve eq15679 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15679
  have eq18709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18709
    | exact resolve eq18709 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18709
  have eq18721 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18710
       have r₂ := eq27
       grind)
    | exact resolve eq18710 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18710
  have eq18723 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18721
    | exact resolve eq18721 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18721
  have eq18725 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18723
    | exact resolve eq18723 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18723
  have eq18727 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18725 eq96
    | (have r₁ := eq96
       have r₂ := eq18725
       grind)
    | exact resolve eq96 eq18725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq18725
  have eq18804 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq18727
  have eq18805 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq18804
  have eq18946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18805 eq94
    | exact resolve eq94 eq18805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18805
  have eq18954 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18946
  have eq18956 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18954
       have r₂ := eq27
       grind)
    | exact resolve eq18954 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18954
  have eq18958 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18956
       grind)
    | exact superpose eq18956 eq95
    | (have r₁ := eq95
       have r₂ := eq18956
       grind)
    | exact resolve eq95 eq18956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18995 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq18956
       grind)
    | exact superpose eq18956 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18956
       grind)
    | exact resolve eq12 eq18956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18956
  have eq19032 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18995
  have eq19033 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19032
  have eq19034 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18958
  have eq19035 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19034
  have eq19263 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq19033
       grind)
    | exact superpose eq19033 eq43
    | exact resolve eq43 eq19033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq19033
  have eq19278 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19263
    | exact resolve eq19263 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19263
  have eq19388 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19035
       grind)
    | exact superpose eq19035 eq80
    | exact resolve eq80 eq19035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19035
  have eq19402 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19388
    | exact resolve eq19388 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19388
  have eq19573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19402 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq19402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19402
  have eq19576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19573
    | exact resolve eq19573 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19573
  have eq19587 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19576
       have r₂ := eq27
       grind)
    | exact resolve eq19576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19576
  have eq19589 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19587
    | exact resolve eq19587 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19587
  have eq19591 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19589
    | exact resolve eq19589 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19589
  have eq19592 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19591
  have eq19633 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19592 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19592
       grind)
    | exact resolve eq12 eq19592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19592
  have eq19670 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19633
  have eq19671 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19670
  have eq19976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19671 eq19278
    | exact resolve eq19278 eq19671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19278 eq19671
  have eq19978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19976
  have eq19980 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19978
       have r₂ := eq27
       grind)
    | exact resolve eq19978 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19978
  have eq19982 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19980 eq27
    | exact resolve eq27 eq19980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19983 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19980 eq51
    | (have r₁ := eq51
       have r₂ := eq19980
       grind)
    | exact resolve eq51 eq19980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq20014 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19980 eq2137
    | exact resolve eq2137 eq19980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20017 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19983
  have eq20018 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq20014
    | exact resolve eq20014 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20014
  have eq20135 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20017 eq90
    | exact resolve eq90 eq20017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq20136 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20017 eq94
    | exact resolve eq94 eq20017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq20017
  have eq20148 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq20136
  have eq20159 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq20135
    | exact resolve eq20135 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20135
  have eq20164 : y = (k y x) := by
    first
    | (have r₁ := eq20159
       have r₂ := eq50
       grind)
    | exact resolve eq20159 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq20159
  have eq20170 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq20164
       grind)
    | exact superpose eq20164 eq80
    | exact resolve eq80 eq20164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20186 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq20170
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20170
    | exact resolve eq20170 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20170
  have eq21060 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq20148
       grind)
    | exact superpose eq20148 eq95
    | (have r₁ := eq95
       have r₂ := eq20148
       grind)
    | exact resolve eq95 eq20148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq20148
  have eq21136 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21060
  have eq21137 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq21136
  have eq21160 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21137
       have i₂ := eq20164
       grind)
    | exact superpose eq20164 eq21137
    | exact resolve eq21137 eq20164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21137
  have eq21171 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21160 eq29
    | exact resolve eq29 eq21160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21160
  have eq21344 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq21171
    | exact resolve eq21171 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq21171
  have eq21345 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21344
  have eq21356 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21345 eq20
    | exact resolve eq20 eq21345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21450 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq21501 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21356
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21356
    | exact resolve eq21356 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21356
  have eq21599 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21501 eq2137
    | exact resolve eq2137 eq21501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137
  have eq21608 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21501 eq20018
    | exact resolve eq20018 eq21501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20018 eq21501
  have eq21620 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq21608
  have eq21831 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21620 eq1770
    | exact resolve eq1770 eq21620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770 eq21620
  have eq21930 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19980 eq21831
    | exact resolve eq21831 eq19980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21831
  have eq21973 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq21930
  have eq22754 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19980 eq21599
    | exact resolve eq21599 eq19980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19980 eq21599
  have eq22800 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq22754
  have eq25100 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22800 eq21973
    | exact resolve eq21973 eq22800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21973 eq22800
  have eq25139 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq25100
  have eq25182 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25139 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq25139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25139
  have eq25219 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq25182
  have eq25225 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25219
       have r₂ := eq19982
       grind)
    | exact resolve eq25219 eq19982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19982 eq25219
  have eq25346 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25225 eq146
    | exact resolve eq146 eq25225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq25225
  have eq25364 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq25346
    | exact resolve eq25346 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25346
  have eq25373 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq210 eq25364
    | exact resolve eq25364 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq56270 : (σ (k (k y x) (M.op x y))) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq15771 (k y x)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq15771
    | exact resolve eq15771 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq15771
  have eq56363 : (M.op (σ (M.op x y)) (σ y)) = (σ (k (k y x) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) := by
    first
    | exact superpose eq20186 eq56270
    | exact resolve eq56270 eq20186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56270
  have eq56380 : (M.op (σ (M.op x y)) (σ y)) = (k (k (σ y) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) := by
    first
    | exact superpose eq189 eq56363
    | exact resolve eq56363 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq56363
  have eq56390 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) := by
    first
    | exact superpose eq20186 eq56380
    | exact resolve eq56380 eq20186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56380
  have eq56397 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20186 eq56390
    | exact resolve eq56390 eq20186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20186 eq56390
  have eq56415 : (k y (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq56397 eq109
    | exact resolve eq109 eq56397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq56397
  have eq948665 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq25373 eq1869
    | exact resolve eq1869 eq25373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869 eq25373
  have eq975803 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq948665 eq25364
    | exact resolve eq25364 eq948665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25364 eq948665
  have eq975895 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq975803
  have eq976040 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq975895 eq1772
    | exact resolve eq1772 eq975895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772 eq975895
  have eq976543 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21345 eq976040
    | exact resolve eq976040 eq21345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21345 eq976040
  have eq976949 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq976543
       have r₂ := eq21450
       grind)
    | exact resolve eq976543 eq21450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21450 eq976543
  have eq976993 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq976949
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq976949
    | exact resolve eq976949 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976949
  have eq976994 : x = (M.op x y) := by grind
  clear eq976993
  have eq976999 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq976994 eq20
    | exact resolve eq20 eq976994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq977002 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq976994 eq56
    | exact resolve eq56 eq976994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq977105 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | exact superpose eq976994 eq1697
    | exact resolve eq1697 eq976994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq977109 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq976994 eq1737
    | exact resolve eq1737 eq976994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq977464 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq977109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq977109
    | exact resolve eq977109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq977109
  have eq977531 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq976999
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq976999
    | exact resolve eq976999 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976999
  have eq977543 : x = (M.op y y) := by
    first
    | exact superpose eq976994 eq977464
    | exact resolve eq977464 eq976994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977464
  have eq977567 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq977531 eq26
    | exact resolve eq26 eq977531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq978533 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq357
       have i₂ := eq977543
       grind)
    | exact superpose eq977543 eq357
    | exact resolve eq357 eq977543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq978710 : x ≠ x ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq977543
       grind)
    | exact superpose eq977543 eq12
    | exact resolve eq12 eq977543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977543
  have eq978990 : x = (k y y) ∨ x = y := by grind
  clear eq978710
  have eq979288 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq978533
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq978533
    | exact resolve eq978533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978533
  have eq979367 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq977531 eq979288
    | exact resolve eq979288 eq977531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979288
  have eq979492 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq977567 eq56415
    | exact resolve eq56415 eq977567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56415
  have eq979971 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq979492
       have r₂ := eq27
       grind)
    | exact resolve eq979492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979492
  have eq980013 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq976994 eq979971
    | exact resolve eq979971 eq976994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979971
  have eq980027 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq980013
       have i₂ := eq20164
       grind)
    | exact superpose eq20164 eq980013
    | exact resolve eq980013 eq20164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20164 eq980013
  have eq980061 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq980027 eq15
    | exact resolve eq15 eq980027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980027
  have eq980702 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq980061
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq980061
    | exact resolve eq980061 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980061
  have eq980825 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq980702 eq27
    | exact resolve eq27 eq980702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980702
  have eq998888 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12295 y y
       have i₂ := eq978990
       grind)
    | exact superpose eq978990 eq12295
    | (have j0 := eq12295 y y
       grind)
    | exact resolve eq12295 eq978990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12295 eq978990
  have eq998900 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq998888
  have eq998911 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq998900
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq998900
    | exact resolve eq998900 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998900
  have eq998973 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq998911
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq998911
    | exact resolve eq998911 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998911
  have eq999035 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq998973
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq998973
    | exact resolve eq998973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998973
  have eq999081 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq977531 eq999035
    | exact resolve eq999035 eq977531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999035
  have eq1001061 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 X0) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6316 y (M.op x (M.op X0 X0)) x
       have i₂ := eq977002 X0
       grind)
    | exact superpose eq977002 eq6316
    | exact resolve eq6316 eq977002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6316 eq977002
  have eq1001339 : ∀ X0 X1 : G, (M.op y (M.op x (M.op (M.op X1 X0) X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq976994 eq1001061
    | exact resolve eq1001061 eq976994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976994 eq1001061
  have eq1067331 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq977105 (M.op (M.op X1 X0) X0)
       have i₂ := eq1001339 X0 X1
       grind)
    | exact superpose eq1001339 eq977105
    | exact resolve eq977105 eq1001339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977105 eq1001339
  have eq1067898 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X1 X0) X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1067331 X0 X1
       have i₂ := eq6199 X0 (M.op (M.op X1 X0) X0)
       grind)
    | exact superpose eq6199 eq1067331
    | exact resolve eq1067331 eq6199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6199 eq1067331
  have eq1068275 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1
    first
    | exact superpose eq6210 eq1067898
    | exact resolve eq1067898 eq6210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6210 eq1067898
  have eq1068418 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1068275 X0 X1
       have i₂ := eq1466 X0 X0 X1
       grind)
    | exact superpose eq1466 eq1068275
    | exact resolve eq1068275 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466 eq1068275
  have eq1068465 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1068418 X0 X1
       have i₂ := eq460 X0 X0
       grind)
    | exact superpose eq460 eq1068418
    | exact resolve eq1068418 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq1068418
  have eq1462696 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq999081 eq1839
    | exact resolve eq1839 eq999081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839 eq999081
  have eq1952361 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1462696 eq979367
    | exact resolve eq979367 eq1462696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979367 eq1462696
  have eq1952438 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq1952361
  have eq1952469 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1952438
       have r₂ := eq980825
       grind)
    | exact resolve eq1952438 eq980825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952438
  have eq1960166 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1952469 eq1068465
    | exact resolve eq1068465 eq1952469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068465 eq1952469
  have eq1960265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq977567 eq1960166
    | exact resolve eq1960166 eq977567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977567 eq1960166
  have eq1960674 : x = y := by
    first
    | (have r₁ := eq1960265
       have r₂ := eq27
       grind)
    | exact resolve eq1960265 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1960265
  have eq1961227 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1960674
       grind)
    | exact superpose eq1960674 eq24
    | exact resolve eq24 eq1960674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1960674
  have eq1962429 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1961227
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1961227
    | exact resolve eq1961227 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1961227
  have eq1962693 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq977531 eq1962429
    | exact resolve eq1962429 eq977531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977531 eq1962429
  have eq1962811 : False := by grind
  exact eq1962811

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  have eq47 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  clear eq37
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  clear eq85
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq113 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq371 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X1 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq48
    | exact resolve eq48 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq393 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq49 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq50 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq49 X0 x x X3
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 (σ X0) X1 X2 X3
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq49
    | (have j1 := eq63 X0 X0
       grind)
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq629 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq633 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq632 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq634 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq629 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq637 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq624 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq642 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq634 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq634 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq634 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq634 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq652 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq642
    | (have j0 := eq642 X0 X1
       grind)
    | exact resolve eq642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq1623 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 (M.op X0 X0))
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq47
    | exact resolve eq47 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1624 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (M.op X0 (M.op X0 X0))
       have i₂ := eq393 X0 X0 X0
       grind)
    | exact superpose eq393 eq48
    | exact resolve eq48 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1861 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq1623 X0
       grind)
    | exact superpose eq1623 eq371
    | exact resolve eq371 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq1890 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1623 eq372
    | exact resolve eq372 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1902 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq372 eq1890
    | exact resolve eq1890 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890
  have eq1937 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq47 eq1861
    | exact resolve eq1861 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq1861
  have eq2102 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1624 eq372
    | exact resolve eq372 eq1624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624
  have eq2114 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq372 eq2102
    | exact resolve eq2102 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq2102
  have eq4120 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq633 y
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq633
    | (have j0 := eq633 y
       grind)
    | exact resolve eq633 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq4124 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4120
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4120
    | exact resolve eq4120 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120
  have eq4130 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4124
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4124
    | exact resolve eq4124 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq11128 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq374 (σ X0) (σ X0) (σ (k X0 X0)) (M.op x x)
       have i₂ := eq637 X0 x x (σ X0)
       grind)
    | exact superpose eq637 eq374
    | (have j1 := eq637 X0 x x x
       grind)
    | exact resolve eq374 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq637
  have eq11221 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq652
  have eq11339 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq11221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11221
  have eq17576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq17577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17576
    | exact resolve eq17576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17576
  have eq17588 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17577
       have r₂ := eq28
       grind)
    | exact resolve eq17577 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17577
  have eq17590 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17588
    | exact resolve eq17588 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17588
  have eq17593 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq17590
  have eq17689 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17593 eq95
    | exact resolve eq95 eq17593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq17593
  have eq17714 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq17689
    | exact resolve eq17689 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17689
  have eq20145 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq17714
  have eq20210 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20145
  have eq20259 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq631 x y
       have i₂ := eq20210
       grind)
    | exact superpose eq20210 eq631
    | (have j0 := eq631 x y
       grind)
    | exact resolve eq631 eq20210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq20260 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq20210
       grind)
    | exact superpose eq20210 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq20210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20210
  have eq20261 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20260
  have eq20262 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20259
  have eq20265 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20261
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20261
    | exact resolve eq20261 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20261
  have eq20266 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20265
  have eq20267 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20262
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20262
    | exact resolve eq20262 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20262
  have eq20280 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20267
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20267
    | exact resolve eq20267 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20267
  have eq20284 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20280
    | exact resolve eq20280 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20280
  have eq20285 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20284
  have eq20289 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20285
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20285
    | exact resolve eq20285 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20285
  have eq20293 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20289
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20289
    | exact resolve eq20289 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20289
  have eq20332 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1937 x
       have i₂ := eq20266
       grind)
    | exact superpose eq20266 eq1937
    | exact resolve eq1937 eq20266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20339 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x x
       have i₂ := eq20266
       grind)
    | exact superpose eq20266 eq50
    | exact resolve eq50 eq20266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20266
  have eq20382 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20339
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20339
    | exact resolve eq20339 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20339
  have eq20472 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20293 eq1937
    | exact resolve eq1937 eq20293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20479 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20293 eq50
    | exact resolve eq50 eq20293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq20293
  have eq20518 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20479
    | exact resolve eq20479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20479
  have eq20535 : y ≠ y ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq20332
       grind)
    | exact superpose eq20332 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20332
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20332
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq20332
       grind)
    | exact resolve eq12 eq20332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20332
  have eq20568 : x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20535
  have eq20582 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20568
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20568
    | exact resolve eq20568 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20568
  have eq20844 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20472 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20472
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq20472
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20472
       grind)
    | exact resolve eq12 eq20472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20472
  have eq20877 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20844
  have eq20888 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20877
    | exact resolve eq20877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20877
  have eq143108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq20582
       grind)
    | exact superpose eq20582 eq45
    | exact resolve eq45 eq20582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq20582
  have eq143144 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq143108
    | exact resolve eq143108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143108
  have eq145496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143144 eq20888
    | exact resolve eq20888 eq143144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20888 eq143144
  have eq145504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq145496
  have eq145507 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq145504
       have r₂ := eq28
       grind)
    | exact resolve eq145504 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145504
  have eq145869 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq145507 eq20518
    | exact resolve eq20518 eq145507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20518 eq145507
  have eq146077 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq145869
  have eq146129 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20382
       have i₂ := eq146077
       grind)
    | exact superpose eq146077 eq20382
    | exact resolve eq20382 eq146077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20382 eq146077
  have eq146349 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq146129
  have eq146410 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq146349 eq28
    | exact resolve eq28 eq146349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146411 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq146349 eq48
    | exact resolve eq48 eq146349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq146451 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq146349 eq2114
    | exact resolve eq2114 eq146349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114
  have eq146463 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq146451
    | exact resolve eq146451 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146451
  have eq146503 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  have eq146742 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq146349 eq146503
    | exact resolve eq146503 eq146349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146503
  have eq146753 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq146742
  have eq146759 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq146753 eq58
    | exact resolve eq58 eq146753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq146753
  have eq146796 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq146759
    | exact resolve eq146759 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq146759
  have eq146820 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq146796
       grind)
    | exact superpose eq146796 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq146796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146821 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq146820
  have eq154368 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq146463 eq146411
    | exact resolve eq146411 eq146463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146411 eq146463
  have eq154474 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq154368
  have eq154589 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq146349 eq154474
    | exact resolve eq154474 eq146349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146349 eq154474
  have eq154684 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq154589
  have eq155207 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq154684 eq393
    | exact resolve eq393 eq154684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq154684
  have eq155329 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq155207 x
       have i₂ := eq427 sF3 x
       grind)
    | exact superpose eq427 eq155207
    | exact resolve eq155207 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq155207
  have eq259148 : y ≠ y ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq146821
       grind)
    | exact superpose eq146821 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq146821
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq146821
       grind)
    | exact resolve eq12 eq146821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259158 : y = (k (M.op x y) y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq375 x y
       have i₂ := eq146821
       grind)
    | exact superpose eq146821 eq375
    | exact resolve eq375 eq146821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq146821
  have eq259249 : y ≠ y ∨ x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq259148
  have eq259250 : x = (M.op y y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq259249
  have eq259313 : y = (k (M.op x y) y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq259158
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq259158
    | exact resolve eq259158 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259158
  have eq259318 : (M.op x y) = (k x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq259250
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq259250
    | exact resolve eq259250 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259250
  have eq264700 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq259313 eq113
    | exact resolve eq113 eq259313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259313
  have eq264746 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq264700
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq264700
    | exact resolve eq264700 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264700
  have eq266674 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq146796
       have i₂ := eq259318
       grind)
    | exact superpose eq259318 eq146796
    | exact resolve eq146796 eq259318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146796 eq259318
  have eq266686 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq266674
  have eq266833 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1937 y
       have i₂ := eq266686
       grind)
    | exact superpose eq266686 eq1937
    | exact resolve eq1937 eq266686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266686
  have eq267073 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq266833
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq266833
    | exact resolve eq266833 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266833
  have eq267074 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq267073
  have eq267106 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq267074 eq21
    | exact resolve eq21 eq267074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267120 : (σ (k y y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq267074 eq113
    | exact resolve eq113 eq267074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq267074
  have eq267705 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq267120
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq267120
    | exact resolve eq267120 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq267120
  have eq267718 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq267106
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq267106
    | exact resolve eq267106 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267106
  have eq270093 : (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq267705 eq4130
    | exact resolve eq4130 eq267705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130 eq267705
  have eq1240351 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264746 eq270093
    | (have r₁ := eq270093
       have r₂ := eq264746
       grind)
    | exact resolve eq270093 eq264746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264746 eq270093
  have eq1240363 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1240351
  have eq1240364 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1240363
  have eq1261844 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1240364 eq155329
    | exact resolve eq155329 eq1240364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155329 eq1240364
  have eq1262462 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1261844
  have eq1262715 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1937 y
       have i₂ := eq1262462
       grind)
    | exact superpose eq1262462 eq1937
    | exact resolve eq1937 eq1262462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262462
  have eq1263395 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1262715
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1262715
    | exact resolve eq1262715 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262715
  have eq1263396 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1263395
  have eq1263966 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1263396 eq267718
    | exact resolve eq267718 eq1263396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267718 eq1263396
  have eq1264548 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1263966
  have eq1264889 : x = (M.op x y) := by
    first
    | (have r₁ := eq1264548
       have r₂ := eq146410
       grind)
    | exact resolve eq1264548 eq146410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146410 eq1264548
  have eq1265004 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1264889 eq21
    | exact resolve eq21 eq1264889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1265114 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1264889 eq1902
    | exact resolve eq1902 eq1264889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq1265521 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1265114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1265114
    | exact resolve eq1265114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1265114
  have eq1265588 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1265004
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1265004
    | exact resolve eq1265004 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265004
  have eq1265595 : x = (M.op y y) := by
    first
    | exact superpose eq1264889 eq1265521
    | exact resolve eq1265521 eq1264889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265521
  have eq1269156 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1265588 eq27
    | exact resolve eq27 eq1265588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1270125 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq1265595
       grind)
    | exact superpose eq1265595 eq105
    | exact resolve eq105 eq1265595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1270314 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11339 y
       have i₂ := eq1265595
       grind)
    | exact superpose eq1265595 eq11339
    | exact resolve eq11339 eq1265595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11339 eq1265595
  have eq1270983 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1270314
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1270314
    | exact resolve eq1270314 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270314
  have eq1271086 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1270125
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1270125
    | exact resolve eq1270125 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270125
  have eq1271179 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1270983
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1270983
    | exact resolve eq1270983 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270983
  have eq1271201 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1265588 eq1271086
    | exact resolve eq1271086 eq1265588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271086
  have eq1271237 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq1271179
    | exact resolve eq1271179 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271179
  have eq1271256 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1271237
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1271237
    | exact resolve eq1271237 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271237
  have eq1271262 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1271256
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1271256
    | exact resolve eq1271256 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271256
  have eq1271266 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1265588 eq1271262
    | exact resolve eq1271262 eq1265588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271262
  have eq1318243 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq1271201 eq104
    | exact resolve eq104 eq1271201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1318501 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq1318243
    | exact resolve eq1318243 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1318243
  have eq1318526 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq1264889 eq1318501
    | exact resolve eq1318501 eq1264889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264889 eq1318501
  have eq1318684 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1271266 eq1937
    | exact resolve eq1937 eq1271266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937 eq1271266
  have eq1319503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1269156 eq1318684
    | exact resolve eq1318684 eq1269156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269156 eq1318684
  have eq1319630 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1319503
       have r₂ := eq28
       grind)
    | exact resolve eq1319503 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319503
  have eq1319750 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1319630 eq28
    | exact resolve eq28 eq1319630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1321583 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq11128 y
       have i₂ := eq1318526
       grind)
    | exact superpose eq1318526 eq11128
    | (have j0 := eq11128 y
       grind)
    | exact resolve eq11128 eq1318526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11128 eq1318526
  have eq1321672 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1321583
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1321583
    | exact resolve eq1321583 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321583
  have eq1321837 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1321672
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1321672
    | exact resolve eq1321672 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321672
  have eq1322001 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq1321837
    | exact resolve eq1321837 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1321837
  have eq1322149 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1319630 eq1322001
    | exact resolve eq1322001 eq1319630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319630 eq1322001
  have eq1322282 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1322149
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1322149
    | exact resolve eq1322149 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322149
  have eq1322283 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq1322282
  have eq1322526 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq1322283
  have eq1323687 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1322526 eq1271201
    | exact resolve eq1271201 eq1322526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271201 eq1322526
  have eq1323862 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1323687
  have eq1323931 : x = y := by
    first
    | (have r₁ := eq1323862
       have r₂ := eq1319750
       grind)
    | exact resolve eq1323862 eq1319750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323862
  have eq1323991 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1323931
       grind)
    | exact superpose eq1323931 eq25
    | exact resolve eq25 eq1323931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1323931
  have eq1325139 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1323991
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1323991
    | exact resolve eq1323991 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1323991
  have eq1325348 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1265588 eq1325139
    | exact resolve eq1325139 eq1265588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265588 eq1325139
  have eq1325444 : False := by grind
  exact eq1325444

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq26 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq46 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq49 (τ X0)
       grind)
    | exact superpose eq49 eq19
    | exact resolve eq19 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq88
    | exact resolve eq88 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq88
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq178 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq26
    | exact resolve eq26 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq100 (M.op X0 X0)
       grind)
    | exact superpose eq100 eq178
    | exact resolve eq178 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq190 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq187
    | exact resolve eq187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq187
  have eq192 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq100 X1
       grind)
    | exact superpose eq100 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq223 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq192 y x
       grind)
    | exact superpose eq192 eq16
    | (have j1 := eq192 y x
       grind)
    | exact resolve eq16 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq863 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq223
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq223
    | (have j1 := eq14 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq223
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq223
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq223 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq864 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq863
  have eq12989 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq864
       grind)
    | exact superpose eq864 eq16
    | exact resolve eq16 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq12990 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12989
       have r₂ := eq100 x
       grind)
    | exact resolve eq12989 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12989
  have eq350988 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12990
       grind)
    | exact superpose eq12990 eq10
    | exact resolve eq10 eq12990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12990
  have eq351296 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq350988
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq350988
    | exact resolve eq350988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350988
  have eq671648 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq351296
       grind)
    | exact superpose eq351296 eq16
    | exact resolve eq16 eq351296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351296
  have eq671649 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq671648
       have r₂ := eq100 x
       grind)
    | exact resolve eq671648 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq671648
  have eq671735 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq671649
       grind)
    | exact superpose eq671649 eq10
    | exact resolve eq10 eq671649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671649
  have eq672165 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq671735
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq671735
    | exact resolve eq671735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671735
  have eq672166 : y = (M.op x x) := by grind
  clear eq672165
  have eq672261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq190 x
       have i₂ := eq672166
       grind)
    | exact superpose eq672166 eq190
    | exact resolve eq190 eq672166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq672166
  have eq672999 : False := by grind
  exact eq672999

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_x_pxy_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  clear eq22
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq56
    | exact resolve eq56 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq59 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq66 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq66 X0 (σ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq66
    | exact resolve eq66 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq102 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq60 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq95
    | exact resolve eq95 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq95
  have eq126 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq85 X0 (τ X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq85
    | exact resolve eq85 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq133 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq59 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq126
    | exact resolve eq126 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq126
  have eq136 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq136 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq136
    | (have j0 := eq136 (σ X0) (σ X1)
       grind)
    | exact resolve eq136 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq136 (τ X0) X1
       grind)
    | exact superpose eq136 eq17
    | (have j1 := eq136 (τ X0) X1
       grind)
    | exact resolve eq17 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq136
  have eq196 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0
       have i₂ := eq30 X0 X0 X0 X1
       grind)
    | exact superpose eq30 eq133
    | exact resolve eq133 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq197 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0
       have i₂ := eq30 X0 X0 X0 X1
       grind)
    | exact superpose eq30 eq102
    | exact resolve eq102 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq102
  have eq267 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X1) (M.op (M.op X2 (σ X1)) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq137 X0 X1
       grind)
    | exact superpose eq137 eq9
    | (have j1 := eq137 X0 X1
       grind)
    | exact resolve eq9 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq1192 : ∀ X0 X1 : G, (M.op X0 (τ (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq196 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq196
    | exact resolve eq196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1727 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq140
    | exact resolve eq140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq1781 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1727 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1727
    | (have j0 := eq1727 X0 X1
       grind)
    | exact resolve eq1727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq7174 : ∀ X1 X2 : G, (τ (σ X2)) = (M.op (τ (σ X2)) (τ (σ X1))) ∨ (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq196 (σ X2) x
       have i₂ := eq267 X1 X2 x
       grind)
    | exact superpose eq267 eq196
    | (have j1 := eq267 X1 X2 X2
       grind)
    | exact resolve eq196 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq267
  have eq7276 : ∀ X1 X2 : G, (τ (σ X2)) = (M.op (τ (σ X2)) X1) ∨ (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq7174 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7174
    | (have j0 := eq7174 X1 X2
       grind)
    | exact resolve eq7174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7174
  have eq7296 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X1 X2)) ∨ (M.op X2 X1) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq7276 X1 x
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7276
    | (have j0 := eq7276 X1 X2
       grind)
    | exact resolve eq7276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7276
  have eq7320 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7296 x y
       grind)
    | exact superpose eq7296 eq16
    | (have j1 := eq7296 x y
       grind)
    | exact resolve eq16 eq7296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7296
  have eq7386 : y = (M.op y x) := by
    first
    | (have j1 := eq1781 x y
       grind)
    | (have r₁ := eq7320
       have r₂ := eq1781 x y
       grind)
    | exact resolve eq7320 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781 eq7320
  have eq7390 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq7386
       grind)
    | exact superpose eq7386 eq9
    | exact resolve eq9 eq7386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7391 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq7386
       grind)
    | exact superpose eq7386 eq9
    | exact resolve eq9 eq7386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7534 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq197 y x
       have i₂ := eq7391 x
       grind)
    | exact superpose eq7391 eq197
    | exact resolve eq197 eq7391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq7391
  have eq7652 : x = (M.op x (τ (M.op (σ x) (M.op (σ y) (σ x))))) := by
    first
    | (have i₁ := eq1192 x (σ y)
       have i₂ := eq7534
       grind)
    | exact superpose eq7534 eq1192
    | exact resolve eq1192 eq7534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq7700 : x = (M.op x (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7652
       have i₂ := eq7534
       grind)
    | exact superpose eq7534 eq7652
    | exact resolve eq7652 eq7534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7534 eq7652
  have eq10603 : (M.op x (M.op y x)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7390 (τ (M.op (σ x) (σ y)))
       have i₂ := eq7700
       grind)
    | exact superpose eq7700 eq7390
    | exact resolve eq7390 eq7700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7390 eq7700
  have eq10651 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10603
       have i₂ := eq7386
       grind)
    | exact superpose eq7386 eq10603
    | exact resolve eq10603 eq7386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7386 eq10603
  have eq10820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq10651
       grind)
    | exact superpose eq10651 eq11
    | exact resolve eq11 eq10651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10651
  have eq10844 : False := by grind
  exact eq10844

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
    | (have r₁ := eq12 (k X0 X1) (M.op X0 X0)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq179 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : (M.op x y) = (k y x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
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
  have eq789 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq789
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq789
    | exact resolve eq789 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq904 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq781
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq781
    | exact resolve eq781 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq1049 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq904
       grind)
    | exact superpose eq904 eq40
    | exact resolve eq40 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq1050 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1049
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1049
    | exact resolve eq1049 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1052 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq1050
    | exact resolve eq1050 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1052 eq896
    | exact resolve eq896 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq1052
  have eq1759 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq1752
       have r₂ := eq27
       grind)
    | exact resolve eq1752 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq1770 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1759 eq182
    | exact resolve eq182 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq1772 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq180 eq1770
    | exact resolve eq1770 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq1770
  have eq1773 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1772
  have eq1784 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq182 x X0
       have i₂ := eq1773
       grind)
    | exact superpose eq1773 eq182
    | exact resolve eq182 eq1773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq1773
  have eq1786 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq179 eq1784
    | exact resolve eq1784 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1784
  have eq1787 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1786
  have eq1792 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1787 eq32
    | exact resolve eq32 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1787
  have eq1831 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1792
    | exact resolve eq1792 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1792
  have eq1832 : x = y := by grind
  clear eq1831
  have eq1835 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1832
       grind)
    | exact superpose eq1832 eq18
    | exact resolve eq18 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1836 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1832
       grind)
    | exact superpose eq1832 eq24
    | exact resolve eq24 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1832
  have eq1858 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1836
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1836
    | exact resolve eq1836 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1859 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1835
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1835
    | exact resolve eq1835 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1862 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1858 eq26
    | exact resolve eq26 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1858
  have eq1902 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1862
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq1862
    | exact resolve eq1862 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1862
  have eq1908 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1859
       grind)
    | exact superpose eq1859 eq40
    | exact resolve eq40 eq1859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1859
  have eq1915 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1908
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1908
    | exact resolve eq1908 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1908
  have eq1919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1902 eq1915
    | exact resolve eq1915 eq1902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902 eq1915
  have eq1923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1919
    | exact resolve eq1919 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1919
  have eq1925 : False := by grind
  exact eq1925

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq177 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : (M.op x y) = (k y x) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
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
  have eq765 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq765
       have i₂ := eq183 sF2
       grind)
    | exact superpose eq183 eq765
    | exact resolve eq765 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq880 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq757
       have i₂ := eq183 x
       grind)
    | exact superpose eq183 eq757
    | exact resolve eq757 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1020 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq880
       grind)
    | exact superpose eq880 eq39
    | exact resolve eq39 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq1021 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1020
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1020
    | exact resolve eq1020 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1023 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq1021
    | exact resolve eq1021 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1023 eq872
    | exact resolve eq872 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq1023
  have eq1714 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq1707
       have r₂ := eq27
       grind)
    | exact resolve eq1707 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq1725 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1714 eq187
    | exact resolve eq187 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq1727 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq178 eq1725
    | exact resolve eq1725 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1725
  have eq1728 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1727
  have eq1739 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq187 x X0
       have i₂ := eq1728
       grind)
    | exact superpose eq1728 eq187
    | exact resolve eq187 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq1728
  have eq1741 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq177 eq1739
    | exact resolve eq1739 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1739
  have eq1742 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1741
  have eq1747 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1742 eq31
    | exact resolve eq31 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1742
  have eq1786 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1747
    | exact resolve eq1747 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1747
  have eq1787 : x = y := by grind
  clear eq1786
  have eq1790 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq18
    | exact resolve eq18 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1791 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1787
       grind)
    | exact superpose eq1787 eq24
    | exact resolve eq24 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1787
  have eq1813 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1791
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1791
    | exact resolve eq1791 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791
  have eq1814 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1790
       have i₂ := eq183 x
       grind)
    | exact superpose eq183 eq1790
    | exact resolve eq1790 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1817 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1813 eq26
    | exact resolve eq26 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1813
  have eq1857 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1817
       have i₂ := eq183 sF2
       grind)
    | exact superpose eq183 eq1817
    | exact resolve eq1817 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1817
  have eq1863 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1814
       grind)
    | exact superpose eq1814 eq39
    | exact resolve eq39 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1814
  have eq1870 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1863
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1863
    | exact resolve eq1863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1863
  have eq1875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1857 eq1870
    | exact resolve eq1870 eq1857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857 eq1870
  have eq1879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1875
    | exact resolve eq1875 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1875
  have eq1881 : False := by grind
  exact eq1881

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pyx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  clear eq43
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq75
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq75 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by
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
  have eq97 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq115 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq115 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq115 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq115 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq121 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq116 sF2
       grind)
    | exact superpose eq116 eq49
    | exact resolve eq49 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq122 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq121
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq121
    | exact resolve eq121 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq121
  have eq449 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq2090 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq14
    | exact resolve eq14 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2090 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq2090
    | exact resolve eq2090 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2110 eq69
    | (have j0 := eq69 (σ y) (σ x)
       grind)
    | exact resolve eq69 eq2110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2110
  have eq2130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq2129
    | exact resolve eq2129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129
  have eq2133 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq2130
       have r₂ := eq27
       grind)
    | exact resolve eq2130 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2153 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ y) (M.op (σ y) (σ x)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2133 eq449
    | exact resolve eq449 eq2133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2160 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2153 x
       have i₂ := eq449 sF2 x sF3
       grind)
    | exact superpose eq449 eq2153
    | exact resolve eq2153 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq2153
  have eq2181 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2160 eq29
    | exact resolve eq29 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2160
  have eq2204 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq2181
    | exact resolve eq2181 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2181
  have eq2205 : x = y := by grind
  clear eq2204
  have eq2208 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2205
       grind)
    | exact superpose eq2205 eq18
    | exact resolve eq18 eq2205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2209 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2205
       grind)
    | exact superpose eq2205 eq24
    | exact resolve eq24 eq2205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2205
  have eq2243 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2209
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2209
    | exact resolve eq2209 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2209
  have eq2249 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2243 eq26
    | exact resolve eq26 eq2243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2243
  have eq2310 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2249 eq122
    | exact resolve eq122 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq2249
  have eq2342 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2310
       have i₂ := eq2208
       grind)
    | exact superpose eq2208 eq2310
    | exact resolve eq2310 eq2208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208 eq2310
  have eq2346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2342 eq15
    | exact resolve eq15 eq2342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq2372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2346
    | exact resolve eq2346 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2346
  have eq2377 : False := by grind
  exact eq2377
