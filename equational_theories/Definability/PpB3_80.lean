import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_pyy_pxy_Equation4554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq52 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op X2 x) X2 X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X4) X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 x x X0 X4
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X3 X4 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X3 X0) ∨ (M.op (M.op X0 X1) X0) = (k (M.op X3 X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op (M.op X2 X3) X2) X0
       have r₂ := eq14 X0 (M.op X2 X3) X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ X2 ∨ (M.op X0 (M.op X1 X2)) = (k X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X2 (M.op X2 X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op (M.op X2 X3) X2) X0
       have r₂ := eq14 X0 (M.op X2 X3) X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq87 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq81
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq100 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
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
  have eq111 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    grind
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq98
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (k y (k y y))) = (k (σ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq37 (k y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq37
    | exact resolve eq37 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq121 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq116
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq158 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq141
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq141
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 : G, (σ (k (k (M.op x y) (M.op x y)) X0)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq141 eq10
    | exact resolve eq10 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq141 eq16
    | exact resolve eq16 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq158
  have eq224 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 X2 x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq54 X0 X3
       have i₂ := eq14 X0 X1 sF3 X3
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq261 eq54
    | exact resolve eq54 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq59 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : (M.op (M.op x y) x) = (k x (M.op x x)) ∨ x = (M.op (M.op x x) x) := by grind
  have eq304 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2 (M.op x x)
       have i₂ := eq59 X2 x
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    intro X1
    first
    | (have i₁ := eq53 X1 (M.op x x)
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq53
    | exact resolve eq53 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq309 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op X1 x)
       have i₂ := eq59 sF3 X1
       grind)
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq60 X0 x
       have i₂ := eq14 X0 x sF2 x
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by grind
  have eq328 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X1
    first
    | exact superpose eq60 eq54
    | exact resolve eq54 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq453 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq492 : ∀ X0 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq55 X0 (M.op x x) X2
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq55
    | exact resolve eq55 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq261 eq55
    | exact resolve eq55 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq261
  have eq844 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X4 X0 X2 (M.op x x)
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq52
    | exact resolve eq52 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 X3))) ≠ X3 ∨ (M.op X0 (M.op X1 (M.op X2 X3))) = (k X3 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X2 (M.op X2 x)
       have i₂ := eq52 X0 X1 X2 X3 x
       grind)
    | exact superpose eq52 eq13
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1997 : ∀ X2 : G, x ≠ (M.op (M.op x y) x) ∨ (M.op (M.op x y) x) = (k x (M.op x X2)) := by
    intro X2
    first
    | (have i₁ := eq73 x x x x
       have i₂ := eq59 x x
       grind)
    | exact superpose eq59 eq73
    | exact resolve eq73 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2000 : ∀ X2 : G, (σ x) ≠ (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) X2)) := by
    intro X2
    first
    | exact superpose eq60 eq73
    | exact resolve eq73 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2189 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X3 X2) (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op X3 X2) X4) (M.op X3 X2)) ∨ (M.op X3 X2) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3 X4
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f2189_13 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
      intro X0 X1
      grind
    have f2189_14 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
      intro X0 X1 X2 X3 X4
      grind
    have f2189_23 : (k (M.op X3 X2) (M.op X0 (M.op X1 X2))) ≠ (M.op (M.op (M.op X3 X2) X4) (M.op X3 X2)) := by grind
    have f2189_24 : (M.op X3 X2) ≠ (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) := by grind
    have f2189_100 : ∀ X0 X1 : G, (M.op X3 X2) ≠ (M.op X0 (M.op X1 X2)) := by
      intro X0 X1
      first
      | (have i₁ := f2189_24
         have i₂ := f2189_14 (M.op X0 (M.op X1 X2)) X3 X2 X0 X1
         grind)
      | (have i₁ := f2189_24
         have i₂ := f2189_14 X0 X1 X2 (M.op X0 (M.op X1 X2)) X3
         grind)
      | exact superpose f2189_14 f2189_24
      | exact resolve f2189_24 f2189_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2189_173 : ∀ X0 X1 : G, (M.op (M.op (M.op X3 X2) X4) (M.op X3 X2)) ≠ (k (M.op X3 X2) (M.op X0 (M.op X1 X2))) := by
      intro X0 X1
      first
      | (have i₁ := f2189_23
         have i₂ := f2189_14 X0 X1 X2 X0 X1
         grind)
      | (have i₁ := f2189_23
         have i₂ := f2189_14 X0 X1 X2 X0 X1
         grind)
      | exact superpose f2189_14 f2189_23
      | exact resolve f2189_23 f2189_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2189_1967 : ∀ X0 : G, (M.op (M.op (M.op X3 X2) X4) (M.op X3 X2)) ≠ (M.op (M.op (M.op X3 X2) X0) (M.op X3 X2)) ∨ (M.op X3 X2) = (M.op (M.op (M.op X3 X2) (M.op X3 X2)) (M.op X3 X2)) := by
      intro X0
      first
      | (have i₁ := f2189_173 (M.op X3 X2) X3
         have i₂ := f2189_13 (M.op X3 X2) X0
         grind)
      | exact superpose f2189_13 f2189_173
      | (have j1 := f2189_13 (M.op X3 X2) x
         grind)
      | (have r₁ := f2189_173 (M.op X3 X2) X3
         have r₂ := f2189_13 (M.op X3 X2) X4
         grind)
      | exact resolve f2189_173 f2189_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2189_1971 : ∀ X0 : G, (M.op (M.op (M.op X3 X2) X4) (M.op X3 X2)) ≠ (M.op (M.op (M.op X3 X2) X0) (M.op X3 X2)) := by
      intro X0
      first
      | (have j0 := f2189_1967 X0
         grind)
      | (have r₁ := f2189_1967 X0
         have r₂ := f2189_100 (M.op (M.op X3 X2) (M.op X3 X2)) X3
         grind)
      | exact resolve f2189_1967 f2189_100
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2189_1973 : False := by
      first
      | (have r₁ := f2189_1971 x
         have r₂ := f2189_14 (M.op (M.op X3 X2) X4) X3 X2 (M.op (M.op X3 X2) x) X3
         grind)
      | (have r₁ := f2189_1971 x
         have r₂ := f2189_14 (M.op (M.op X3 X2) x) X3 X2 (M.op (M.op X3 X2) X4) X3
         grind)
      | exact resolve f2189_1971 f2189_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f2189_1973
  clear eq61
  have eq2262 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) X1) (τ X0))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq111 (τ X0) X1
       grind)
    | exact superpose eq111 eq35
    | (have j1 := eq111 (τ X0) X1
       grind)
    | exact resolve eq35 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2458 : ∀ X0 X2 X3 : G, (M.op X2 X0) ≠ (M.op (M.op (M.op x y) x) X0) ∨ (M.op (M.op (M.op x y) x) X0) = (k (M.op X2 X0) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq72 X0 (M.op x x) X2 X3
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq72
    | exact resolve eq72 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2533 : ∀ X0 X2 X3 : G, (M.op X0 (M.op x y)) ≠ (M.op X2 (M.op x y)) ∨ (M.op X0 (M.op x y)) = (k (M.op X2 (M.op x y)) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq224 eq72
    | (have r₁ := eq72 (M.op x y) x X2 X2
       have r₂ := eq224 (M.op (M.op x y) x) X2
       grind)
    | (have r₁ := eq72 (M.op x y) x X2 X0
       have r₂ := eq224 X0 (M.op (M.op x y) x)
       grind)
    | exact resolve eq72 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2538 : ∀ X1 X2 : G, (M.op X1 (M.op x y)) ≠ (M.op (M.op (M.op x y) x) y) ∨ (M.op (M.op (M.op x y) x) y) = (k (M.op X1 (M.op x y)) X2) := by
    intro X1 X2
    first
    | exact superpose eq308 eq72
    | exact resolve eq72 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq2648 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) x) y) = (k (M.op X1 (M.op x y)) X2) := by
    intro X1 X2
    first
    | (have j0 := eq2538 X1 X2
       grind)
    | (have r₁ := eq2538 X1 X2
       have r₂ := eq308 X1
       grind)
    | exact resolve eq2538 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq2538
  have eq2653 : ∀ X0 X2 X3 : G, (M.op X0 (M.op x y)) = (k (M.op X2 (M.op x y)) X3) := by
    intro X0 X2 X3
    first
    | (have j0 := eq2533 X0 X2 X3
       grind)
    | (have r₁ := eq2533 X0 X2 X3
       have r₂ := eq224 X0 X2
       grind)
    | (have r₁ := eq2533 X2 X0 X3
       have r₂ := eq224 X0 X2
       grind)
    | exact resolve eq2533 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533
  have eq4522 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 (M.op x y))) X2) = (σ (M.op X0 (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2653 eq39
    | exact resolve eq39 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2653
  have eq5853 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op (M.op x y) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq262 eq492
    | exact resolve eq492 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq38997 : x = (M.op (M.op x y) x) ∨ (M.op (M.op x y) x) = (k x (M.op x x)) := by
    first
    | (have i₁ := eq299
       have i₂ := eq298 x
       grind)
    | exact superpose eq298 eq299
    | exact resolve eq299 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq299
  have eq38998 : (M.op (M.op x y) x) = (k x (M.op x x)) := by
    first
    | (have j1 := eq1997 x
       grind)
    | (have r₁ := eq38997
       have r₂ := eq1997 x
       grind)
    | exact resolve eq38997 eq1997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997 eq38997
  have eq39094 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq317 eq318
    | exact resolve eq318 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq318
  have eq39095 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have j1 := eq2000 (σ x)
       grind)
    | (have r₁ := eq39094
       have r₂ := eq2000 x
       grind)
    | exact resolve eq39094 eq2000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000 eq39094
  have eq60967 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq78
    | (have j0 := eq78 x
       grind)
    | exact resolve eq78 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq61037 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq60967
  have eq61070 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61037
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq61037
    | exact resolve eq61037 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61037
  have eq61085 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq61070
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq61070 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61070
  have eq61093 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq61085 eq50
    | exact resolve eq50 eq61085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq61164 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq100 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq100
    | (have j0 := eq100 y
       grind)
    | exact resolve eq100 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq61234 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq61164
  have eq61262 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq61234
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq61234
    | exact resolve eq61234 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61234
  have eq61273 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq61262
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq61262 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61262
  have eq61282 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq61273 eq121
    | exact resolve eq121 eq61273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq61347 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq142
    | (have j0 := eq142 (M.op x y)
       grind)
    | exact resolve eq142 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq61414 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq61347
  have eq61441 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq141 eq61414
    | exact resolve eq61414 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61414
  have eq61454 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq61441
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq61441 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61441
  have eq61465 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq61454 eq164
    | exact resolve eq164 eq61454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq63345 : ∀ X0 X1 : G, (σ (M.op X0 (M.op x y))) = (σ (k (M.op X1 (M.op x y)) y)) := by
    intro X0 X1
    first
    | exact superpose eq4522 eq41
    | exact resolve eq41 eq4522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq63382 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (σ (M.op (M.op (M.op x y) x) y)) := by
    intro X0
    first
    | exact superpose eq2648 eq63345
    | exact resolve eq63345 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63345
  have eq64465 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op x y) x) X3) ≠ X3 ∨ (M.op X0 (M.op X1 (M.op X2 X3))) = (k X3 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq951 X0 X1 X2 X3 X4
       have i₂ := eq844 X3 X0 X1 X2
       grind)
    | exact superpose eq844 eq951
    | (have j0 := eq951 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq951 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq64466 : ∀ X3 X4 : G, (M.op (M.op (M.op x y) x) X3) ≠ X3 ∨ (k X3 (M.op X3 X4)) = (M.op (M.op (M.op x y) x) X3) := by
    intro X3 X4
    first
    | (have i₁ := eq64465 x x x X3 X4
       have i₂ := eq844 X3 x x x
       grind)
    | exact superpose eq844 eq64465
    | (have j0 := eq64465 x x x X3 X4
       grind)
    | exact resolve eq64465 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq64465
  have eq74424 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (M.op x y) x) (τ X0))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2262 X0 x
       have i₂ := eq492 (τ X0) x
       grind)
    | exact superpose eq492 eq2262
    | (have j0 := eq2262 X0 x
       grind)
    | exact resolve eq2262 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq74425 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (M.op x y) x) (τ X0))) ∨ (τ X0) = (M.op (M.op (M.op x y) x) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq74424 X0
       have i₂ := eq492 (τ X0) (τ X0)
       grind)
    | exact superpose eq492 eq74424
    | (have j0 := eq74424 X0
       grind)
    | exact resolve eq74424 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq74424
  have eq74521 : ∀ X0 : G, (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) = (τ (σ (M.op (M.op (M.op x y) x) (τ (σ X0))))) ∨ (τ (σ X0)) = (M.op (M.op (M.op x y) x) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq453 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq74425 (σ X0)
       grind)
    | exact superpose eq74425 eq453
    | (have j1 := eq74425 (σ X0)
       grind)
    | exact resolve eq453 eq74425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq74425
  have eq74545 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (τ (σ X0))) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op (M.op (M.op x y) x) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq74521 X0
       have i₂ := eq16 (M.op (M.op sF0 x) (τ (σ X0)))
       grind)
    | exact superpose eq16 eq74521
    | (have j0 := eq74521 X0
       grind)
    | exact resolve eq74521 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74521
  have eq74588 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (τ (σ X0))) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (M.op (M.op x y) x) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq74545 X0
       have i₂ := eq16 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq16 eq74545
    | (have j0 := eq74545 X0
       grind)
    | exact resolve eq74545 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74545
  have eq74609 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op (M.op x y) x) X0) ∨ (τ (σ X0)) = (M.op (M.op (M.op x y) x) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq74588 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq74588
    | (have j0 := eq74588 X0
       grind)
    | exact resolve eq74588 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74588
  have eq74612 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have i₁ := eq74609 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq74609
    | (have j0 := eq74609 X0
       grind)
    | exact resolve eq74609 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74609
  have eq74615 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have j0 := eq74612 X0
       have j1 := eq64466 X0 X0
       grind)
    | (have r₁ := eq74612 x
       have r₂ := eq64466 x x
       grind)
    | exact resolve eq74612 eq64466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64466 eq74612
  have eq90597 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) x) X2) = (k (M.op X3 X2) (M.op X0 (M.op X1 X2))) ∨ (M.op X3 X2) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2189 X0 X1 X2 X3 x
       have i₂ := eq304 (M.op (M.op X3 X2) x) X3 X2
       grind)
    | exact superpose eq304 eq2189
    | (have j0 := eq2189 X0 X1 X2 X3 x
       grind)
    | exact resolve eq2189 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189
  have eq90598 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) x) X2) = (M.op X3 X2) ∨ (M.op (M.op (M.op x y) x) X2) = (k (M.op X3 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq90597 X0 X1 X2 X3
       have i₂ := eq304 (M.op X0 (M.op X1 X2)) X3 X2
       grind)
    | exact superpose eq304 eq90597
    | (have j0 := eq90597 X0 X1 X2 X3
       grind)
    | exact resolve eq90597 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90597
  have eq90599 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) x) X2) = (k (M.op X3 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq90598 X0 X1 X2 X3
       have j1 := eq2458 X2 X3 (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq90598 X0 X1 X0 (M.op (M.op x y) x)
       have r₂ := eq2458 X0 (M.op (M.op x y) x) X3
       grind)
    | (have r₁ := eq90598 X0 X1 X0 X2
       have r₂ := eq2458 X0 X2 X3
       grind)
    | exact resolve eq90598 eq2458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2458 eq90598
  have eq102895 : (σ (k y (k y y))) = (k (σ y) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq61273 eq117
    | exact resolve eq117 eq61273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq102896 : (σ (k y (k y y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | (have i₁ := eq102895
       have i₂ := eq74615 sF3
       grind)
    | exact superpose eq74615 eq102895
    | exact resolve eq102895 eq74615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102895
  have eq107488 : (k y (k y y)) = (τ (M.op (M.op (M.op x y) x) (σ y))) := by
    first
    | (have i₁ := eq16 (k y (k y y))
       have i₂ := eq102896
       grind)
    | exact superpose eq102896 eq16
    | exact resolve eq16 eq102896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102896
  have eq112163 : ∀ X0 : G, (k y (k y y)) = (τ (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq309 eq107488
    | exact resolve eq107488 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq107488
  have eq116675 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq61085 eq87
    | exact resolve eq87 eq61085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq117078 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq61273 eq122
    | exact resolve eq122 eq61273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq118274 : ∀ X0 : G, (σ (k (k (M.op x y) (M.op x y)) X0)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq61454 eq163
    | exact resolve eq163 eq61454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq118279 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq61454 eq165
    | exact resolve eq165 eq61454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq152394 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq116675
       grind)
    | exact superpose eq116675 eq16
    | exact resolve eq16 eq116675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116675
  have eq152465 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq61093 eq152394
    | exact resolve eq152394 eq61093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152394
  have eq152477 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq152465
       have r₂ := eq13 x x
       grind)
    | exact resolve eq152465 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152465
  have eq152479 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq152477
       grind)
    | exact superpose eq152477 eq44
    | exact resolve eq44 eq152477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq152530 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq61085 eq152479
    | exact resolve eq152479 eq61085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61085 eq152479
  have eq152567 : (k (σ x) (M.op (σ x) (σ x))) = (σ (k x (M.op x x))) := by
    first
    | (have i₁ := eq36 (M.op x x)
       have i₂ := eq152530
       grind)
    | exact superpose eq152530 eq36
    | exact resolve eq36 eq152530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq152638 : (σ (M.op (M.op x y) x)) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq152567
       have i₂ := eq38998
       grind)
    | exact superpose eq38998 eq152567
    | exact resolve eq152567 eq38998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38998 eq152567
  have eq152650 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq39095 eq152638
    | exact resolve eq152638 eq39095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39095 eq152638
  have eq153312 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq117078
       grind)
    | exact superpose eq117078 eq16
    | exact resolve eq16 eq117078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117078
  have eq153385 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq61282 eq153312
    | exact resolve eq153312 eq61282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61282 eq153312
  have eq153394 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq153385
       have r₂ := eq13 y y
       grind)
    | exact resolve eq153385 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153385
  have eq153395 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq153394
       grind)
    | exact superpose eq153394 eq98
    | exact resolve eq98 eq153394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq153402 : ∀ X0 : G, (k y (M.op y y)) = (τ (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq112163 X0
       have i₂ := eq153394
       grind)
    | exact superpose eq153394 eq112163
    | exact resolve eq112163 eq153394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112163 eq153394
  have eq153450 : ∀ X0 : G, (M.op (M.op (M.op x y) x) y) = (τ (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq153402 X0
       have i₂ := eq74615 y
       grind)
    | exact superpose eq74615 eq153402
    | exact resolve eq153402 eq74615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74615 eq153402
  have eq153452 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq61273 eq153395
    | exact resolve eq153395 eq61273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61273 eq153395
  have eq153673 : ∀ X0 X1 : G, (σ (M.op X1 (M.op x y))) = (σ (τ (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq153450 eq63382
    | exact resolve eq63382 eq153450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63382 eq153450
  have eq153894 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (σ (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq153673 X0 X1
       have i₂ := eq15 (M.op X0 sF4)
       grind)
    | exact superpose eq15 eq153673
    | exact resolve eq153673 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153673
  have eq156438 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq118279 eq16
    | exact resolve eq16 eq118279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118279
  have eq156532 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq61465 eq156438
    | exact resolve eq156438 eq61465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61465 eq156438
  have eq156546 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq156532
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq156532 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156532
  have eq156552 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq156546 eq141
    | exact resolve eq141 eq156546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq156606 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq61454 eq156552
    | exact resolve eq156552 eq61454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61454 eq156552
  have eq156632 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq224 eq156606
    | exact resolve eq156606 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq156636 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq153894 eq156606
    | exact resolve eq156606 eq153894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153894 eq156606
  have eq156767 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq288 eq156636
    | exact resolve eq156636 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq157734 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op X0 (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq156632 eq4522
    | exact resolve eq4522 eq156632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4522
  have eq157847 : ∀ X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) X1) := by
    intro X1
    first
    | exact superpose eq156632 eq157734
    | exact resolve eq157734 eq156632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156632 eq157734
  have eq157912 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq157847 (M.op x (M.op x sF1))
       have i₂ := eq90599 x x sF1 sF1
       grind)
    | exact superpose eq90599 eq157847
    | exact resolve eq157847 eq90599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90599
  have eq158107 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq304 eq157912
    | exact resolve eq157912 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq157912
  have eq175894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175906 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq175894
    | exact resolve eq175894 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175894
  have eq175917 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq175906
       have r₂ := eq28
       grind)
    | exact resolve eq175906 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175906
  have eq175922 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq175917 eq61093
    | exact resolve eq61093 eq175917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175917
  have eq176126 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq175922
       have i₂ := eq152477
       grind)
    | exact superpose eq152477 eq175922
    | exact resolve eq175922 eq152477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175922
  have eq176153 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq176126
    | exact resolve eq176126 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176126
  have eq176154 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq176153
  have eq176167 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq176154 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq176154
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq176154
       grind)
    | exact resolve eq13 eq176154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176154
  have eq176237 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq176167
  have eq176334 : (τ (σ x)) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq176237 eq66
    | exact resolve eq66 eq176237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq176335 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq176237 eq90
    | exact resolve eq90 eq176237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq176237
  have eq176354 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq176335
  have eq176362 : y = (M.op x x) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq176334
    | exact resolve eq176334 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq176334
  have eq176414 : (k x y) = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq111 x x
       have i₂ := eq176354
       grind)
    | exact superpose eq176354 eq111
    | exact resolve eq111 eq176354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176354
  have eq176479 : (k x y) = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq176414
  have eq176532 : (k x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq176479
       have r₂ := eq13 x y
       grind)
    | exact resolve eq176479 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176479
  have eq176584 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq176532
       grind)
    | exact superpose eq176532 eq45
    | exact resolve eq45 eq176532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176743 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (k (σ x) (σ y))) = (σ (k (k (M.op x y) (M.op x y)) (M.op y x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq118274 (M.op y x)
       have i₂ := eq176584
       grind)
    | exact superpose eq176584 eq118274
    | exact resolve eq118274 eq176584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118274 eq176584
  have eq176746 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (k (σ x) (σ y))) = (σ (k (M.op (M.op x y) (M.op x y)) (M.op y x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq156546 eq176743
    | exact resolve eq176743 eq156546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156546 eq176743
  have eq176755 : (σ (M.op (M.op (M.op x y) x) y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (k (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2648 eq176746
    | exact resolve eq176746 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq176746
  have eq176756 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) x) y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq157847 eq176755
    | exact resolve eq176755 eq157847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157847 eq176755
  have eq176973 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op X0 (M.op (σ x) (σ y))) y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq5853 eq176756
    | exact resolve eq176756 eq5853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5853 eq176756
  have eq177681 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq156636 eq176973
    | exact resolve eq176973 eq156636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176973
  have eq179295 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (σ (M.op (M.op X0 (M.op (σ x) (σ y))) y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq156636 eq177681
    | exact resolve eq177681 eq156636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156636 eq177681
  have eq179575 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (σ (M.op (M.op y X0) y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq179295 y
       have i₂ := eq499 X0 y sF4
       grind)
    | exact superpose eq499 eq179295
    | exact resolve eq179295 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179295
  have eq291401 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq152530
       have i₂ := eq176362
       grind)
    | exact superpose eq176362 eq152530
    | exact resolve eq152530 eq176362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152530
  have eq291446 : (k x y) = (M.op y x) ∨ x = (M.op y x) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq111 x x
       have i₂ := eq176362
       grind)
    | exact superpose eq176362 eq111
    | exact resolve eq111 eq176362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176362
  have eq291514 : (k x y) = (M.op y x) ∨ x = (M.op y x) ∨ x = (k x y) := by grind
  clear eq291446
  have eq291570 : (k x y) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq291514
       have r₂ := eq13 x y
       grind)
    | exact resolve eq291514 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291514
  have eq291598 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq291401
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq291401
    | exact resolve eq291401 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq291401
  have eq291644 : x ≠ (M.op y x) ∨ x = (k x y) := by grind
  clear eq291570
  have eq293790 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq291598
       have r₂ := eq291644
       grind)
    | exact resolve eq291598 eq291644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291598 eq291644
  have eq293792 : (τ (σ y)) = (k x x) ∨ x = (k x y) := by
    first
    | exact superpose eq293790 eq61093
    | exact resolve eq61093 eq293790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61093
  have eq293802 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X0 (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq293790 eq60
    | exact resolve eq60 eq293790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq293790
  have eq293976 : (τ (σ y)) = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq293792
       have i₂ := eq152477
       grind)
    | exact superpose eq152477 eq293792
    | exact resolve eq293792 eq152477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152477 eq293792
  have eq294004 : y = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq30 eq293976
    | exact resolve eq293976 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq293976
  have eq294020 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq59 X0 x
       have i₂ := eq294004
       grind)
    | exact superpose eq294004 eq59
    | exact resolve eq59 eq294004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294004
  have eq294371 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    intro X0 X1
    first
    | exact superpose eq293802 eq293802
    | exact resolve eq293802 eq293802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293802
  have eq294877 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (k x y) := by
    intro X0 X1
    first
    | (have j0 := eq294371 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294371
  have eq295745 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (k x y) ∨ x = (k x y) := by
    intro X0 X1
    first
    | exact superpose eq294020 eq294020
    | exact resolve eq294020 eq294020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294020
  have eq296339 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0 X1
    first
    | (have j0 := eq295745 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295745
  have eq300194 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq27 eq294877
    | (have j0 := eq294877 X0 (σ x)
       grind)
    | exact resolve eq294877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294877
  have eq309656 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq296339 X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq296339
    | (have j0 := eq296339 X0 x
       grind)
    | exact resolve eq296339 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296339
  have eq311198 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq153452
       have i₂ := eq309656 y
       grind)
    | exact superpose eq309656 eq153452
    | exact resolve eq153452 eq309656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153452 eq309656
  have eq311238 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq21 eq311198
    | exact resolve eq311198 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311198
  have eq312772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq311238 eq300194
    | exact resolve eq300194 eq311238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300194 eq311238
  have eq312876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq312772
  have eq312941 : x = (k x y) := by
    first
    | (have r₁ := eq312876
       have r₂ := eq28
       grind)
    | exact resolve eq312876 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312876
  have eq313018 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq312941
       have i₂ := eq176532
       grind)
    | exact superpose eq176532 eq312941
    | exact resolve eq312941 eq176532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176532
  have eq313025 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq312941
       grind)
    | exact superpose eq312941 eq45
    | exact resolve eq45 eq312941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq312941
  have eq313069 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq313025
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq313025
    | exact resolve eq313025 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313025
  have eq313199 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq179575 x X0
       have i₂ := eq313018
       grind)
    | exact superpose eq313018 eq179575
    | exact resolve eq179575 eq313018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179575
  have eq313203 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq59 X0 y
       have i₂ := eq313018
       grind)
    | exact superpose eq313018 eq59
    | exact resolve eq59 eq313018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq313280 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq313199 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313199
  have eq313341 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq313280 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq313280
    | (have j0 := eq313280 X0
       grind)
    | exact resolve eq313280 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq313280
  have eq313368 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq21 eq313341
    | (have j0 := eq313341 X0
       grind)
    | exact resolve eq313341 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq313341
  have eq322326 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq313203 X0
       have i₂ := eq313203 sF0
       grind)
    | exact superpose eq313203 eq313203
    | exact resolve eq313203 eq313203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313203
  have eq322792 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq322326 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322326
  have eq356917 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq313018
       have i₂ := eq322792 X0 y
       grind)
    | (have i₁ := eq313018
       have i₂ := eq322792 y X0
       grind)
    | exact superpose eq322792 eq313018
    | exact resolve eq313018 eq322792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313018 eq322792
  have eq357011 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq356917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356917
  have eq357812 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq152650
       have i₂ := eq357011 sF0
       grind)
    | exact superpose eq357011 eq152650
    | exact resolve eq152650 eq357011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152650 eq357011
  have eq357902 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq357812
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq357812
    | exact resolve eq357812 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq357812
  have eq358378 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq357902 eq328
    | exact resolve eq328 eq357902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq357902
  have eq358531 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq27 eq358378
    | (have j0 := eq358378 X0
       grind)
    | exact resolve eq358378 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358378
  have eq360058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq358531 eq313368
    | exact resolve eq313368 eq358531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313368 eq358531
  have eq360373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq360058
  have eq360576 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq360373
       have r₂ := eq28
       grind)
    | exact resolve eq360373 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360373
  have eq360773 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq360576 eq27
    | exact resolve eq27 eq360576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq360886 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq360576 eq313069
    | exact resolve eq313069 eq360576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313069 eq360576
  have eq361780 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq360886 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq360886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq360773 eq361780
    | exact resolve eq361780 eq360773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361780
  have eq361809 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq361797
       have r₂ := eq28
       grind)
    | exact resolve eq361797 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361797
  have eq391404 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq361809 eq111
    | exact resolve eq111 eq361809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq361809
  have eq391483 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq391404
  have eq391560 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq391483
       have r₂ := eq13 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq391483 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391483
  have eq391637 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq360886 eq391560
    | exact resolve eq391560 eq360886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360886 eq391560
  have eq391730 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq391637 eq158107
    | exact resolve eq158107 eq391637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158107
  have eq391759 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq391637 eq499
    | exact resolve eq499 eq391637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq391871 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq156767 eq391759
    | exact resolve eq391759 eq156767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156767 eq391759
  have eq391927 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq360773 eq391871
    | exact resolve eq391871 eq360773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360773 eq391871
  have eq426700 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq391927 eq391730
    | exact resolve eq391730 eq391927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391730 eq391927
  have eq427216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq426700 eq391637
    | exact resolve eq391637 eq426700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391637 eq426700
  have eq427225 : False := by grind
  exact eq427225

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyy_pxx_pyx_Equation4554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
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
  have eq52 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op X2 x) X2 X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X4) X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 x x X0 X4
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 X3 X4 (M.op x X0)
       have i₂ := eq14 X4 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 X0) ∨ (M.op (M.op X0 X1) X0) = (k X3 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 (M.op X1 X2) X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X2 X3) X2)
       have r₂ := eq14 (M.op (M.op X2 X3) X2) (M.op X2 X3) X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq88 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq95 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq88
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq80
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq104
  have eq119 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq142 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq159 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq142
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq142
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq159
  have eq180 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq194 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq41
    | exact resolve eq41 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq217 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq219 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x y)) = (M.op (M.op (M.op X0 X1) X0) y) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X3 (M.op x X0)
       have i₂ := eq14 y x X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 X2 x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X3 x
       have i₂ := eq14 X0 X1 y x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) X0) (σ y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq54 X0 (M.op X1 x)
       have i₂ := eq14 sF3 X1 x X3
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (σ y))) := by
    intro X0 X2
    first
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq59 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2 (M.op x x)
       have i₂ := eq59 X2 x
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    intro X1
    first
    | (have i₁ := eq53 X1 (M.op x x)
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq53
    | exact resolve eq53 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq301 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op X1 x)
       have i₂ := eq59 sF3 X1
       grind)
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq308 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq60 X0 x
       have i₂ := eq14 X0 x sF2 x
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq453 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 X4) X2) = (M.op (M.op (M.op X0 X1) X0) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq55 X2 (M.op x X0) X4
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq55 X0 (M.op x x) X2
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq55
    | exact resolve eq55 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq763 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op X4 (M.op X5 (M.op X6 X2))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq52 X5 X6 X2 X4 (M.op x X0)
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X4 X0 X2 (M.op x x)
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq52
    | exact resolve eq52 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq891 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X2 (M.op X3 X0)) ∨ (M.op (M.op X0 X1) X0) = (k X4 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X1 X2))
       have i₂ := eq52 X0 X1 X2 (M.op X0 (M.op X1 X2)) x
       grind)
    | exact superpose eq52 eq13
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X0) = (k X4 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq891 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq891 X2 X3 X0 X1 X4
       have r₂ := eq14 X0 X1 X2 X3
       grind)
    | exact resolve eq891 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq1274 : ∀ X0 X1 X2 X3 X5 X6 X7 : G, (M.op X5 (M.op X6 (M.op X7 X3))) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) := by
    intro X0 X1 X2 X3 X5 X6 X7
    first
    | (have i₁ := eq52 X6 X7 X3 X5 (M.op x X2)
       have i₂ := eq57 X0 X1 X3 x X2
       grind)
    | exact superpose eq57 eq52
    | exact resolve eq52 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1433 : ∀ X0 X1 : G, (k (M.op X1 X1) X1) = (M.op (M.op X0 (M.op x y)) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 X1 (M.op x y)
       have i₂ := eq221 X1 x X0
       grind)
    | (have i₁ := eq119 x (M.op x y)
       have i₂ := eq221 X0 X1 x
       grind)
    | exact superpose eq221 eq119
    | (have j0 := eq119 X1 X1
       grind)
    | exact resolve eq119 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1447 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (k (M.op (M.op X3 X2) (M.op X3 X2)) (M.op X3 X2)) ∨ (M.op X3 X2) = (M.op (M.op X3 X2) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq119 (M.op X3 X2) x
       have i₂ := eq57 X0 X1 (M.op (M.op X3 X2) x) X3 X2
       grind)
    | exact superpose eq57 eq119
    | (have j0 := eq119 (M.op X3 X2) X1
       grind)
    | exact resolve eq119 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2231 : ∀ X0 X2 X3 : G, (M.op X2 X0) ≠ (M.op (M.op (M.op x y) x) X0) ∨ (k X3 (M.op X2 X0)) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq72 X0 (M.op x x) X2 X3
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq72
    | exact resolve eq72 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2306 : ∀ X0 X2 X3 : G, (M.op X0 (M.op x y)) ≠ (M.op X2 (M.op x y)) ∨ (M.op X0 (M.op x y)) = (k X3 (M.op X2 (M.op x y))) := by
    intro X0 X2 X3
    first
    | exact superpose eq220 eq72
    | (have r₁ := eq72 (M.op x y) x X2 X3
       have r₂ := eq220 (M.op (M.op x y) x) X2
       grind)
    | (have r₁ := eq72 (M.op x y) x X0 X3
       have r₂ := eq220 X0 (M.op (M.op x y) x)
       grind)
    | exact resolve eq72 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2316 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (σ x) (σ y))) ≠ (M.op X2 (M.op (σ x) (σ y))) ∨ (M.op X0 (M.op (σ x) (σ y))) = (k X3 (M.op X2 (M.op (σ x) (σ y)))) := by
    intro X0 X2 X3
    first
    | exact superpose eq255 eq72
    | (have r₁ := eq72 (M.op (σ x) (σ y)) x X2 X3
       have r₂ := eq255 (M.op (M.op (σ x) (σ y)) x) X2
       grind)
    | (have r₁ := eq72 (M.op (σ x) (σ y)) x X0 X3
       have r₂ := eq255 X0 (M.op (M.op (σ x) (σ y)) x)
       grind)
    | exact resolve eq72 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2328 : ∀ X0 X1 X3 : G, (M.op (M.op x y) x) ≠ (M.op (M.op (M.op X0 x) X1) (M.op X0 x)) ∨ (M.op (M.op (M.op X0 x) X1) (M.op X0 x)) = (k X3 (M.op (M.op x y) x)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq72 (M.op X1 x) X1 X0 X3
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq72
    | exact resolve eq72 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq2404 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 x) X1) (M.op X0 x)) = (k X3 (M.op (M.op x y) x)) := by
    intro X0 X1 X3
    first
    | (have j0 := eq2328 X0 X1 X3
       grind)
    | (have r₁ := eq2328 X1 X1 X3
       have r₂ := eq59 (M.op (M.op X1 x) X1) X1
       grind)
    | exact resolve eq2328 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328
  have eq2416 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X3 (M.op X2 (M.op (σ x) (σ y)))) := by
    intro X0 X2 X3
    first
    | (have j0 := eq2316 X0 X2 X3
       grind)
    | (have r₁ := eq2316 X0 X2 X3
       have r₂ := eq255 X0 X2
       grind)
    | (have r₁ := eq2316 X2 X0 X3
       have r₂ := eq255 X0 X2
       grind)
    | exact resolve eq2316 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq2316
  have eq2426 : ∀ X0 X2 X3 : G, (M.op X0 (M.op x y)) = (k X3 (M.op X2 (M.op x y))) := by
    intro X0 X2 X3
    first
    | (have j0 := eq2306 X0 X2 X3
       grind)
    | (have r₁ := eq2306 X0 X2 X3
       have r₂ := eq220 X0 X2
       grind)
    | (have r₁ := eq2306 X2 X0 X3
       have r₂ := eq220 X0 X2
       grind)
    | exact resolve eq2306 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306
  have eq2469 : ∀ X3 : G, (M.op (M.op x y) x) = (k X3 (M.op (M.op x y) x)) := by
    intro X3
    first
    | (have i₁ := eq2404 x x X3
       have i₂ := eq59 (M.op (M.op x x) x) x
       grind)
    | exact superpose eq59 eq2404
    | exact resolve eq2404 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2404
  have eq2955 : ∀ X0 X1 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (M.op (σ X0) X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 (σ X0) X1
       have i₂ := eq82 X0 X0
       grind)
    | exact superpose eq82 eq119
    | (have j0 := eq119 (σ X0) X1
       have j1 := eq82 X0 X0
       grind)
    | exact resolve eq119 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq2974 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq82 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2975 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2974 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974
  have eq2980 : ∀ X0 X1 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (M.op (σ X0) X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2955 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq2985 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2980 X0 X1
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq2980
    | (have j0 := eq2980 X0 X1
       grind)
    | exact resolve eq2980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980
  have eq4129 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op X2 (M.op (σ x) (σ y))))) = (τ (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2416 eq441
    | exact resolve eq441 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq4458 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 (M.op x y)))) = (σ (M.op X0 (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2426 eq35
    | exact resolve eq35 eq2426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq17618 : ∀ X0 X1 X2 X3 X4 : G, (k X2 (τ (M.op X3 (M.op X4 X0)))) = (τ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq441 X2 (M.op X3 (M.op X4 X0))
       have i₂ := eq905 X0 X1 X3 X4 (σ X2)
       grind)
    | exact superpose eq905 eq441
    | exact resolve eq441 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq33178 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) x) X2) = (M.op (M.op (M.op X0 X1) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq763 X0 X1 X2 x x x
       have i₂ := eq765 X2 x x x
       grind)
    | exact superpose eq765 eq763
    | exact resolve eq763 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq38029 : (σ (M.op (M.op x y) x)) ≠ (σ (M.op (M.op x y) x)) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq2469 eq2975
    | (have j0 := eq2975 (M.op (M.op x y) x)
       grind)
    | exact resolve eq2975 eq2469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469
  have eq38038 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2975 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq2975
    | (have j0 := eq2975 (τ X0)
       grind)
    | exact resolve eq2975 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38047 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by grind
  clear eq38029
  have eq38053 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38038 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38038
    | (have j0 := eq38038 X0
       grind)
    | exact resolve eq38038 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38038
  have eq38061 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq38053 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38053
    | (have j0 := eq38053 X0
       grind)
    | exact resolve eq38053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38053
  have eq46149 : ∀ X2 X3 X5 X6 X7 : G, (M.op X5 (M.op X6 (M.op X7 X3))) = (M.op (M.op (M.op (M.op x y) x) X2) X3) := by
    intro X2 X3 X5 X6 X7
    first
    | (have i₁ := eq1274 x x X2 X3 X5 X6 X7
       have i₂ := eq33178 x x X2
       grind)
    | (have i₁ := eq1274 x y X2 X3 X5 X6 X7
       have i₂ := eq33178 x x X2
       grind)
    | exact superpose eq33178 eq1274
    | (have j0 := eq1274 x y X2 X3 X5 X6 X7
       grind)
    | exact resolve eq1274 eq33178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq46150 : ∀ X2 X3 : G, (M.op (M.op (M.op x y) x) X3) = (M.op (M.op (M.op (M.op x y) x) X2) X3) := by
    intro X2 X3
    first
    | (have i₁ := eq46149 X2 X3 x x x
       have i₂ := eq765 X3 x x x
       grind)
    | exact superpose eq765 eq46149
    | exact resolve eq46149 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq46149
  have eq52172 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq180
    | (have j0 := eq180 x
       grind)
    | exact resolve eq180 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq52240 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq52172
  have eq52267 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52240
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq52240
    | exact resolve eq52240 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52240
  have eq52283 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq52267
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq52267 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52267
  have eq52289 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq52283 eq50
    | exact resolve eq50 eq52283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq52347 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq202 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq202
    | (have j0 := eq202 y
       grind)
    | exact resolve eq202 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq52415 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq52347
  have eq52437 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq52415
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq52415
    | exact resolve eq52415 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52415
  have eq52452 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq52437
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq52437 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52437
  have eq52460 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq52452 eq109
    | exact resolve eq109 eq52452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq52520 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq217
    | (have j0 := eq217 (M.op x y)
       grind)
    | exact resolve eq217 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq52585 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq52520
  have eq52606 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq142 eq52585
    | exact resolve eq52585 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52585
  have eq52623 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq52606
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq52606 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52606
  have eq52632 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq52623 eq165
    | exact resolve eq165 eq52623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq80738 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2985 X0 X1
       have j1 := eq2975 X0
       grind)
    | (have r₁ := eq2985 X0 X1
       have r₂ := eq2975 X0
       grind)
    | exact resolve eq2985 eq2975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975 eq2985
  have eq80739 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (M.op (M.op (M.op x y) x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq80738 X0 x
       have i₂ := eq454 (σ X0) x
       grind)
    | exact superpose eq454 eq80738
    | (have j0 := eq80738 X0 x
       grind)
    | exact resolve eq80738 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq80738
  have eq80817 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (σ (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (k (τ X0) (τ X0))
       have i₂ := eq80739 (τ X0)
       grind)
    | exact superpose eq80739 eq39
    | (have j1 := eq80739 (τ X0)
       grind)
    | exact resolve eq39 eq80739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq80739
  have eq80988 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = (M.op (M.op (M.op x y) x) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80817 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq80817
    | (have j0 := eq80817 X0
       grind)
    | exact resolve eq80817 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq80817
  have eq81036 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80988 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq80988
    | (have j0 := eq80988 X0
       grind)
    | exact resolve eq80988 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80988
  have eq81051 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op x y) x) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq81036 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq81036
    | (have j0 := eq81036 X0
       grind)
    | exact resolve eq81036 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81036
  have eq81064 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (k (M.op (M.op (M.op x y) x) X2) (M.op X3 X2)) ∨ (M.op X3 X2) = (M.op (M.op X3 X2) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1447 X0 X1 X2 X3
       have i₂ := eq296 (M.op X3 X2) X3 X2
       grind)
    | exact superpose eq296 eq1447
    | (have j0 := eq1447 X0 X1 X2 X3
       grind)
    | exact resolve eq1447 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq81065 : ∀ X2 X3 : G, (M.op (M.op (M.op x y) x) X2) = (k (M.op (M.op (M.op x y) x) X2) (M.op X3 X2)) ∨ (M.op X3 X2) = (M.op (M.op X3 X2) (M.op X3 X2)) := by
    intro X2 X3
    first
    | (have i₁ := eq81064 x x X2 X3
       have i₂ := eq33178 x x X2
       grind)
    | (have i₁ := eq81064 x y X2 X3
       have i₂ := eq33178 x x X2
       grind)
    | exact superpose eq33178 eq81064
    | (have j0 := eq81064 x y X2 X3
       grind)
    | exact resolve eq81064 eq33178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81064
  have eq81066 : ∀ X2 X3 : G, (M.op (M.op (M.op x y) x) X2) = (M.op X3 X2) ∨ (M.op (M.op (M.op x y) x) X2) = (k (M.op (M.op (M.op x y) x) X2) (M.op X3 X2)) := by
    intro X2 X3
    first
    | (have i₁ := eq81065 X2 X3
       have i₂ := eq296 (M.op X3 X2) X3 X2
       grind)
    | exact superpose eq296 eq81065
    | (have j0 := eq81065 X2 X3
       grind)
    | exact resolve eq81065 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81065
  have eq81067 : ∀ X2 X3 : G, (M.op (M.op (M.op x y) x) X2) = (k (M.op (M.op (M.op x y) x) X2) (M.op X3 X2)) := by
    intro X2 X3
    first
    | (have j0 := eq81066 X2 X3
       have j1 := eq2231 X2 X3 (M.op (M.op (M.op x y) x) X2)
       grind)
    | (have r₁ := eq81066 x (M.op (M.op x y) x)
       have r₂ := eq2231 x (M.op (M.op x y) x) X3
       grind)
    | (have r₁ := eq81066 x X2
       have r₂ := eq2231 x X2 X3
       grind)
    | exact resolve eq81066 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231 eq81066
  have eq113537 : (σ (k (k y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq52452 eq194
    | exact resolve eq194 eq52452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq129375 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq52283 eq95
    | exact resolve eq95 eq52283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq130510 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq52452 eq110
    | exact resolve eq110 eq52452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq132823 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq52623 eq166
    | exact resolve eq166 eq52623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq162200 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq129375
       grind)
    | exact superpose eq129375 eq16
    | exact resolve eq16 eq129375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129375
  have eq162272 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq52289 eq162200
    | exact resolve eq162200 eq52289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162200
  have eq162284 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq162272
       have r₂ := eq13 x x
       grind)
    | exact resolve eq162272 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162272
  have eq162477 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq162284
       grind)
    | exact superpose eq162284 eq44
    | exact resolve eq44 eq162284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq162524 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq52283 eq162477
    | exact resolve eq162477 eq52283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52283 eq162477
  have eq163197 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq130510
       grind)
    | exact superpose eq130510 eq16
    | exact resolve eq16 eq130510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130510
  have eq163271 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq52460 eq163197
    | exact resolve eq163197 eq52460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163197
  have eq163281 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq163271
       have r₂ := eq13 x y
       grind)
    | exact resolve eq163271 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163271
  have eq163283 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq163281
       grind)
    | exact superpose eq163281 eq80
    | exact resolve eq80 eq163281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq163330 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq52452 eq163283
    | exact resolve eq163283 eq52452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52452 eq163283
  have eq164610 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq132823 eq16
    | exact resolve eq16 eq132823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132823
  have eq164706 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq52632 eq164610
    | exact resolve eq164610 eq52632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52632 eq164610
  have eq164719 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq164706
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq164706 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164706
  have eq164728 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq164719 eq142
    | exact resolve eq142 eq164719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq164719
  have eq164780 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq52623 eq164728
    | exact resolve eq164728 eq52623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52623 eq164728
  have eq164798 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq220 eq164780
    | exact resolve eq164780 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq164780
  have eq164938 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) x) y)) := by
    first
    | exact superpose eq300 eq164798
    | exact resolve eq164798 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq165027 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq164798 eq4458
    | exact resolve eq4458 eq164798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4458
  have eq165141 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq164798 eq165027
    | exact resolve eq165027 eq164798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164798 eq165027
  have eq165244 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ (M.op x y))) := by
    first
    | exact superpose eq81067 eq165141
    | exact resolve eq165141 eq81067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165141
  have eq165538 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq296 eq165244
    | exact resolve eq165244 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq165244
  have eq178674 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) (σ y)) := by
    intro X0
    first
    | exact superpose eq38047 eq252
    | exact resolve eq252 eq38047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178811 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ (M.op (M.op x y) x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq38047 eq178674
    | exact resolve eq178674 eq38047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38047 eq178674
  have eq181052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq181062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq181052
    | exact resolve eq181052 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181052
  have eq181073 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq181062
       have r₂ := eq28
       grind)
    | exact resolve eq181062 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181062
  have eq181079 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq181073 eq52289
    | exact resolve eq52289 eq181073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181073
  have eq181299 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq181079
       have i₂ := eq162284
       grind)
    | exact superpose eq162284 eq181079
    | exact resolve eq181079 eq162284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181079
  have eq181326 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq181299
    | exact resolve eq181299 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181299
  have eq181327 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq181326
  have eq181348 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq181327 eq52289
    | exact resolve eq52289 eq181327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52289 eq181327
  have eq181541 : (τ (σ x)) = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq181348
       have i₂ := eq162284
       grind)
    | exact superpose eq162284 eq181348
    | exact resolve eq181348 eq162284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162284 eq181348
  have eq181582 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq181541
    | exact resolve eq181541 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq181541
  have eq181583 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq181582
  have eq181628 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq162524
       have i₂ := eq181583
       grind)
    | exact superpose eq181583 eq162524
    | exact resolve eq162524 eq181583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162524
  have eq181633 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq59 X0 x
       have i₂ := eq181583
       grind)
    | exact superpose eq181583 eq59
    | exact resolve eq59 eq181583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181583
  have eq181833 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq181628
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq181628
    | exact resolve eq181628 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181628
  have eq181891 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq181833 eq308
    | exact resolve eq308 eq181833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq181893 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq181833 eq60
    | exact resolve eq60 eq181833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq181833
  have eq182341 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq181633 eq181633
    | exact resolve eq181633 eq181633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181633
  have eq182851 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq182341 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182341
  have eq183260 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq181893 eq181891
    | exact resolve eq181891 eq181893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181891 eq181893
  have eq183616 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq183260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183260
  have eq185588 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq182851 X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq182851
    | (have j0 := eq182851 X0 x
       grind)
    | exact resolve eq182851 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182851
  have eq186855 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq163330
       have i₂ := eq185588 y
       grind)
    | exact superpose eq185588 eq163330
    | exact resolve eq163330 eq185588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163330 eq185588
  have eq186878 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq186855
    | exact resolve eq186855 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186855
  have eq193922 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq183616 eq186878
    | exact resolve eq186878 eq183616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186878
  have eq193925 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq193922
  have eq194120 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq193925 eq183616
    | exact resolve eq183616 eq193925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183616 eq193925
  have eq194210 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq194120 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194120
  have eq194699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq194210 eq27
    | (have j1 := eq194210 (σ x)
       grind)
    | exact resolve eq27 eq194210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194210
  have eq194726 : x = (M.op x x) := by
    first
    | (have r₁ := eq194699
       have r₂ := eq28
       grind)
    | exact resolve eq194699 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194699
  have eq194812 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq290 x
       have i₂ := eq194726
       grind)
    | exact superpose eq194726 eq290
    | exact resolve eq290 eq194726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq194839 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op x x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 x x X0 X1 X2
       have i₂ := eq194726
       grind)
    | exact superpose eq194726 eq57
    | exact resolve eq57 eq194726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq194847 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq219 x x X0
       have i₂ := eq194726
       grind)
    | exact superpose eq194726 eq219
    | exact resolve eq219 eq194726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq194851 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq453 x x X0 X1
       have i₂ := eq194726
       grind)
    | exact superpose eq194726 eq453
    | exact resolve eq453 eq194726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq194966 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq194851 X0 X1
       have i₂ := eq194726
       grind)
    | exact superpose eq194726 eq194851
    | exact resolve eq194851 eq194726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194851
  have eq194970 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq194847 X0
       have i₂ := eq194726
       grind)
    | exact superpose eq194726 eq194847
    | exact resolve eq194847 eq194726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194847
  have eq194976 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq194839 X0 X1 X2
       have i₂ := eq194726
       grind)
    | exact superpose eq194726 eq194839
    | exact resolve eq194839 eq194726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194839
  have eq194999 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq194812
       have i₂ := eq194726
       grind)
    | exact superpose eq194726 eq194812
    | exact resolve eq194812 eq194726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194726 eq194812
  have eq195037 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq194970 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq194970
    | (have j0 := eq194970 X0
       grind)
    | exact resolve eq194970 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194970
  have eq195440 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op x X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq194999 eq81067
    | exact resolve eq81067 eq194999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195447 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq194999 eq164938
    | exact resolve eq164938 eq194999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164938
  have eq195451 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq194999 eq178811
    | exact resolve eq178811 eq194999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178811
  have eq195459 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq194999 eq59
    | exact resolve eq59 eq194999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq195586 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq195451 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq195451
    | (have j0 := eq195451 X0
       grind)
    | exact resolve eq195451 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq195451
  have eq195589 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq195447
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq195447
    | exact resolve eq195447 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195447
  have eq195628 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq195586
    | (have j0 := eq195586 X0
       grind)
    | exact resolve eq195586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq195586
  have eq195629 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq195589
    | exact resolve eq195589 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195589
  have eq196013 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq221 eq195037
    | exact resolve eq195037 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq196430 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq195037 eq46150
    | exact resolve eq46150 eq195037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46150
  have eq196463 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq194999 eq196430
    | exact resolve eq196430 eq194999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196430
  have eq197731 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq195628 eq301
    | exact resolve eq301 eq195628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq197758 : ∀ X0 X2 : G, (τ (M.op X2 (M.op (σ x) (σ y)))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0 X2
    first
    | exact superpose eq195628 eq4129
    | exact resolve eq4129 eq195628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129
  have eq198195 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq195628 eq197758
    | exact resolve eq197758 eq195628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197758
  have eq198213 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq197731
       have i₂ := eq195459 sF0
       grind)
    | exact superpose eq195459 eq197731
    | exact resolve eq197731 eq195459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195459 eq197731
  have eq198359 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq195629 eq165538
    | exact resolve eq165538 eq195629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165538 eq195629
  have eq209507 : ∀ X0 : G, (τ (τ (M.op (σ x) (σ y)))) = (k X0 (τ (τ (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq198195 eq441
    | exact resolve eq441 eq198195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198195
  have eq231730 : (τ (τ (M.op (σ x) (σ y)))) ≠ (τ (τ (M.op (σ x) (σ y)))) ∨ (τ (τ (M.op (σ x) (σ y)))) = (M.op (τ (τ (M.op (σ x) (σ y)))) (τ (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq209507 eq38061
    | (have j0 := eq38061 (τ (τ (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq38061 (τ (τ (M.op (σ x) (σ y))))
       have r₂ := eq209507 (τ (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq38061 eq209507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231812 : (τ (τ (M.op (σ x) (σ y)))) = (M.op (τ (τ (M.op (σ x) (σ y)))) (τ (τ (M.op (σ x) (σ y))))) := by grind
  clear eq231730
  have eq233563 : ∀ X0 X2 X3 X4 : G, (k X2 (τ (M.op X3 (M.op X4 X0)))) = (τ (M.op x X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq17618 X0 x X2 X3 X4
       have i₂ := eq194966 X0 x
       grind)
    | exact superpose eq194966 eq17618
    | exact resolve eq17618 eq194966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17618 eq194966
  have eq233564 : ∀ X0 X2 : G, (τ (M.op x X0)) = (k X2 (τ (M.op x X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq233563 X0 X2 x x
       have i₂ := eq194976 x x X0
       grind)
    | exact superpose eq194976 eq233563
    | exact resolve eq233563 eq194976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194976 eq233563
  have eq233744 : ∀ X0 : G, (τ (M.op x X0)) ≠ (τ (M.op x X0)) ∨ (τ (M.op x X0)) = (M.op (τ (M.op x X0)) (τ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq38061 (τ (M.op x X0))
       have i₂ := eq233564 X0 (τ (M.op x X0))
       grind)
    | exact superpose eq233564 eq38061
    | (have j0 := eq38061 (τ (M.op x X0))
       grind)
    | (have r₁ := eq38061 (τ (M.op x X0))
       have r₂ := eq233564 X0 (τ (M.op x X0))
       grind)
    | exact resolve eq38061 eq233564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38061
  have eq233818 : ∀ X0 X1 : G, (τ (τ (M.op x X0))) = (k X1 (τ (τ (M.op x X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X1 (τ (M.op x X0))
       have i₂ := eq233564 X0 (σ X1)
       grind)
    | exact superpose eq233564 eq441
    | exact resolve eq441 eq233564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq233827 : ∀ X0 : G, (τ (M.op x X0)) = (M.op (τ (M.op x X0)) (τ (M.op x X0))) := by
    intro X0
    first
    | (have j0 := eq233744 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233744
  have eq254502 : (M.op x (τ (τ (M.op (σ x) (σ y))))) = (k (M.op x (τ (τ (M.op (σ x) (σ y))))) (τ (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq231812 eq195440
    | exact resolve eq195440 eq231812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195440 eq231812
  have eq254504 : (τ (τ (M.op (σ x) (σ y)))) = (M.op x (τ (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq209507 eq254502
    | exact resolve eq254502 eq209507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209507 eq254502
  have eq327005 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op x X0)) (τ (M.op x X0))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq252 (τ (M.op x X0)) (τ (M.op x X0)) X1
       have i₂ := eq233827 X0
       grind)
    | exact superpose eq233827 eq252
    | exact resolve eq252 eq233827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq327061 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) X1) = (M.op (M.op (τ (M.op x X0)) (τ (M.op x X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33178 (τ (M.op x X0)) (τ (M.op x X0)) X1
       have i₂ := eq233827 X0
       grind)
    | exact superpose eq233827 eq33178
    | exact resolve eq33178 eq233827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33178
  have eq327074 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (τ (M.op x X0))) = (k (M.op (M.op (M.op x y) x) (τ (M.op x X0))) (τ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq81067 (τ (M.op x X0)) (τ (M.op x X0))
       have i₂ := eq233827 X0
       grind)
    | exact superpose eq233827 eq81067
    | exact resolve eq81067 eq233827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81067
  have eq327101 : ∀ X0 : G, (τ (M.op x X0)) = (M.op (M.op (M.op x y) x) (τ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq327074 X0
       have i₂ := eq233564 X0 (M.op (M.op sF0 x) (τ (M.op x X0)))
       grind)
    | exact superpose eq233564 eq327074
    | exact resolve eq327074 eq233564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233564 eq327074
  have eq327114 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) X1) = (M.op (τ (M.op x X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq327061 X0 X1
       have i₂ := eq233827 X0
       grind)
    | exact superpose eq233827 eq327061
    | exact resolve eq327061 eq233827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327061
  have eq327163 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (τ (M.op x X0)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq327005 X0 X1
       have i₂ := eq233827 X0
       grind)
    | exact superpose eq233827 eq327005
    | exact resolve eq327005 eq233827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233827 eq327005
  have eq327289 : ∀ X0 : G, (τ (M.op x X0)) = (M.op x (τ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq194999 eq327101
    | exact resolve eq327101 eq194999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327101
  have eq327301 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op x X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq194999 eq327114
    | exact resolve eq327114 eq194999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327114
  have eq327340 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (τ (M.op x X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq195628 eq327163
    | exact resolve eq327163 eq195628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195628 eq327163
  have eq339354 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (τ (M.op x X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq327301 (τ (M.op x X0)) X1
       have i₂ := eq327289 X0
       grind)
    | exact superpose eq327289 eq327301
    | exact resolve eq327301 eq327289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327301
  have eq339355 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (τ (τ (M.op x X0))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq327340 (τ (M.op x X0))
       have i₂ := eq327289 X0
       grind)
    | exact superpose eq327289 eq327340
    | exact resolve eq327340 eq327289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327340
  have eq339868 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (τ (τ (τ (M.op x X0)))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq339355 (τ (M.op x X0))
       have i₂ := eq327289 X0
       grind)
    | exact superpose eq327289 eq339355
    | exact resolve eq339355 eq327289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339355
  have eq342376 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (τ (τ (τ (τ (M.op x X0))))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq339868 (τ (M.op x X0))
       have i₂ := eq327289 X0
       grind)
    | exact superpose eq327289 eq339868
    | exact resolve eq339868 eq327289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327289 eq339868
  have eq361911 : ∀ X1 : G, (k (M.op X1 X1) X1) = (M.op (M.op x y) X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | exact superpose eq195037 eq1433
    | (have j0 := eq1433 x X1
       grind)
    | exact resolve eq1433 eq195037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433 eq195037
  have eq361912 : ∀ X1 : G, (k (M.op X1 X1) X1) = (M.op x X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | exact superpose eq196463 eq361911
    | (have j0 := eq361911 X1
       grind)
    | exact resolve eq361911 eq196463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196463 eq361911
  have eq362320 : ∀ X0 : G, (τ (τ (M.op x X0))) = (M.op x (τ (τ (M.op x X0)))) ∨ (τ (τ (M.op x X0))) = (M.op (τ (τ (M.op x X0))) (τ (τ (M.op x X0)))) := by
    intro X0
    first
    | (have i₁ := eq233818 X0 (M.op (τ (τ (M.op x X0))) (τ (τ (M.op x X0))))
       have i₂ := eq361912 (τ (τ (M.op x X0)))
       grind)
    | exact superpose eq361912 eq233818
    | (have j1 := eq361912 (τ (τ (M.op x X0)))
       grind)
    | exact resolve eq233818 eq361912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233818
  have eq362422 : ∀ X0 : G, (τ (τ (M.op x X0))) = (M.op x (τ (τ (M.op x X0)))) ∨ (τ (τ (M.op x X0))) = (M.op x (τ (τ (M.op x X0)))) := by
    intro X0
    first
    | (have i₁ := eq362320 X0
       have i₂ := eq339354 X0 (τ (τ (M.op x X0)))
       grind)
    | exact superpose eq339354 eq362320
    | (have j0 := eq362320 X0
       grind)
    | exact resolve eq362320 eq339354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339354 eq362320
  have eq362423 : ∀ X0 : G, (τ (τ (M.op x X0))) = (M.op x (τ (τ (M.op x X0)))) := by
    intro X0
    first
    | (have j0 := eq362422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362422
  have eq376813 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (τ (τ (τ (τ (τ (τ (M.op x X0))))))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq342376 (τ (τ (M.op x X0)))
       have i₂ := eq362423 X0
       grind)
    | exact superpose eq362423 eq342376
    | exact resolve eq342376 eq362423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342376 eq362423
  have eq384905 : (M.op (σ x) (σ y)) = (M.op (τ (τ (τ (τ (τ (τ (τ (τ (M.op (σ x) (σ y)))))))))) (σ y)) := by
    first
    | exact superpose eq254504 eq376813
    | exact resolve eq376813 eq254504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254504 eq376813
  have eq411363 : ∀ X0 : G, (M.op x X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq194999 eq81051
    | (have j0 := eq81051 X0
       grind)
    | exact resolve eq81051 eq194999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81051 eq194999
  have eq411654 : (σ (M.op x y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq113537
       have i₂ := eq411363 y
       grind)
    | exact superpose eq411363 eq113537
    | (have j1 := eq411363 y
       grind)
    | exact resolve eq113537 eq411363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113537 eq411363
  have eq411669 : (σ (M.op x y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq411654
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq411654
    | exact resolve eq411654 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq411654
  have eq411751 : (σ (M.op x y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq411669
    | exact resolve eq411669 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411669
  have eq411900 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq411751 eq361912
    | (have j0 := eq361912 (σ y)
       grind)
    | exact resolve eq361912 eq411751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361912 eq411751
  have eq411923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq198213 eq411900
    | exact resolve eq411900 eq198213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198213 eq411900
  have eq411971 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq411923
       have r₂ := eq28
       grind)
    | exact resolve eq411923 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411923
  have eq412045 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq411971 eq52460
    | exact resolve eq52460 eq411971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52460 eq411971
  have eq412287 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq412045
       have i₂ := eq163281
       grind)
    | exact superpose eq163281 eq412045
    | exact resolve eq412045 eq163281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163281 eq412045
  have eq412360 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq412287
    | exact resolve eq412287 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq412287
  have eq412361 : y = (M.op y y) := by grind
  clear eq412360
  have eq412532 : ∀ X0 X1 : G, (M.op y y) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 y y
       have i₂ := eq412361
       grind)
    | exact superpose eq412361 eq14
    | exact resolve eq14 eq412361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412688 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq412532 x x
       have i₂ := eq196013 x x
       grind)
    | exact superpose eq196013 eq412532
    | exact resolve eq412532 eq196013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196013 eq412532
  have eq412785 : y = (M.op x y) := by
    first
    | (have i₁ := eq412688
       have i₂ := eq412361
       grind)
    | exact superpose eq412361 eq412688
    | exact resolve eq412688 eq412361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412361 eq412688
  have eq412963 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq412785 eq21
    | exact resolve eq21 eq412785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq412785
  have eq413376 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq412963
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq412963
    | exact resolve eq412963 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq412963
  have eq413808 : (M.op (σ x) (σ y)) = (M.op (τ (τ (τ (τ (τ (τ (τ (τ (M.op (σ x) (σ y)))))))))) (σ (M.op x y))) := by
    first
    | exact superpose eq413376 eq384905
    | exact resolve eq384905 eq413376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384905 eq413376
  have eq413811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq198359 eq413808
    | exact resolve eq413808 eq198359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198359 eq413808
  have eq414024 : False := by grind
  exact eq414024

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pyx_Equation4554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq52 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op X2 x) X2 X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X3 X4 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq84 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq82 (σ X0)
       grind)
    | exact superpose eq82 eq10
    | exact resolve eq10 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq50
    | exact resolve eq50 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq87 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq86
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq86
    | exact resolve eq86 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq84
    | exact resolve eq84 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq96 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq82 sF3
       grind)
    | exact superpose eq82 eq80
    | exact resolve eq80 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq82 y
       grind)
    | exact superpose eq82 eq96
    | exact resolve eq96 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq82 sF1
       grind)
    | exact superpose eq82 eq137
    | exact resolve eq137 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq82 sF0
       grind)
    | exact superpose eq82 eq140
    | exact resolve eq140 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq235 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 X2 x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X3 x
       have i₂ := eq14 X0 X1 y x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq235 eq142
    | exact resolve eq142 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq235
  have eq305 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq270 (M.op sF0 x)
       have i₂ := eq14 X0 X1 sF0 x
       grind)
    | exact superpose eq14 eq270
    | exact resolve eq270 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq59 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2 (M.op x x)
       have i₂ := eq59 X2 x
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    intro X1
    first
    | (have i₁ := eq53 X1 (M.op x x)
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq53
    | exact resolve eq53 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq325 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op X1 x)
       have i₂ := eq59 sF3 X1
       grind)
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X1
    first
    | exact superpose eq60 eq54
    | exact resolve eq54 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq511 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | exact superpose eq236 eq270
    | exact resolve eq270 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq533 : (σ (M.op (k x x) (k x x))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq89 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq89
    | exact resolve eq89 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq548 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq533
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq533
    | exact resolve eq533 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq550 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq548
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq548
    | exact resolve eq548 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq548
  have eq552 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | exact superpose eq60 eq550
    | exact resolve eq550 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq550
  have eq553 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq552
       have i₂ := eq59 (M.op x x) x
       grind)
    | exact superpose eq59 eq552
    | exact resolve eq552 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq749 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) x) y)) := by
    first
    | exact superpose eq324 eq270
    | exact resolve eq270 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq324
  have eq792 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X2 (M.op X3 (σ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0) X2 X3
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq61
    | exact resolve eq61 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq937 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X4 X0 X2 (M.op x x)
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq52
    | exact resolve eq52 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1160 : (M.op (M.op (M.op x y) x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq325 eq340
    | exact resolve eq340 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq340
  have eq4827 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op X1 (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq305 eq89
    | exact resolve eq89 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq4834 : ∀ X1 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op (M.op x y) x) (M.op X1 (M.op x y)))) := by
    intro X1
    first
    | (have i₁ := eq4827 X1 X1
       have i₂ := eq321 (M.op X1 (M.op X1 sF0)) X1 (M.op X1 sF0)
       grind)
    | exact superpose eq321 eq4827
    | exact resolve eq4827 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827
  have eq4842 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq305 eq4834
    | exact resolve eq4834 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq4834
  have eq4843 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4842
       have i₂ := eq321 (M.op sF1 sF1) sF1 sF1
       grind)
    | exact superpose eq321 eq4842
    | exact resolve eq4842 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842
  have eq5173 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq321 eq4843
    | exact resolve eq4843 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq4843
  have eq12208 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op (M.op y y) (M.op y y)))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq792 (M.op y y) X0 X1 X2
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq792
    | exact resolve eq792 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq792
  have eq12450 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12208 X0 X1 X2
       have i₂ := eq511 (M.op y y) y
       grind)
    | exact superpose eq511 eq12208
    | exact resolve eq12208 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq12208
  have eq12492 : ∀ X1 X2 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X1 X2
    first
    | exact superpose eq5173 eq12450
    | exact resolve eq12450 eq5173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5173 eq12450
  have eq37617 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | (have i₁ := eq12492 x x
       have i₂ := eq937 sF3 x x sF3
       grind)
    | exact superpose eq937 eq12492
    | exact resolve eq12492 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq12492
  have eq64242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq64250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq64242
    | exact resolve eq64242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64242
  have eq64255 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq64250
       have r₂ := eq28
       grind)
    | exact resolve eq64250 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64250
  have eq64257 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq64255 eq87
    | exact resolve eq87 eq64255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64255
  have eq64344 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq64257
    | exact resolve eq64257 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64257
  have eq64345 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq64344
  have eq64355 : (M.op (M.op x y) x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq317 x
       have i₂ := eq64345
       grind)
    | exact superpose eq64345 eq317
    | exact resolve eq317 eq64345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq64358 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq59 X0 x
       have i₂ := eq64345
       grind)
    | exact superpose eq64345 eq59
    | exact resolve eq59 eq64345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64873 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq64355
       have i₂ := eq64358 sF0
       grind)
    | exact superpose eq64358 eq64355
    | exact resolve eq64355 eq64358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64355 eq64358
  have eq65061 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq64873 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64873
  have eq66972 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq64345
       have i₂ := eq65061 X0
       grind)
    | (have i₁ := eq64345
       have i₂ := eq65061 x
       grind)
    | exact superpose eq65061 eq64345
    | exact resolve eq64345 eq65061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64345 eq65061
  have eq67225 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq66972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66972
  have eq67534 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq553
       have i₂ := eq67225 sF0
       grind)
    | exact superpose eq67225 eq553
    | exact resolve eq553 eq67225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq67538 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq749
       have i₂ := eq67225 sF0
       grind)
    | exact superpose eq67225 eq749
    | exact resolve eq749 eq67225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq67225
  have eq67587 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67538
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67538
    | exact resolve eq67538 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67538
  have eq67589 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67534
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq67534
    | exact resolve eq67534 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67534
  have eq67666 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq67587
    | exact resolve eq67587 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67587
  have eq67820 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq67589 eq1160
    | exact resolve eq1160 eq67589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq67589
  have eq67901 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq37617 eq67820
    | exact resolve eq67820 eq37617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37617 eq67820
  have eq67906 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq67901
    | exact resolve eq67901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67901
  have eq69071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq67906 eq67666
    | exact resolve eq67666 eq67906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67666 eq67906
  have eq69130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq69071
  have eq69158 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq69130
       have r₂ := eq28
       grind)
    | exact resolve eq69130 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69130
  have eq69173 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq69158 eq30
    | exact resolve eq30 eq69158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq69158
  have eq69269 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq69173
    | exact resolve eq69173 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq69173
  have eq69270 : x = y := by grind
  clear eq69269
  have eq69281 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq69270
       grind)
    | exact superpose eq69270 eq19
    | exact resolve eq19 eq69270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq69282 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq69270
       grind)
    | exact superpose eq69270 eq25
    | exact resolve eq25 eq69270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq69270
  have eq69448 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq69282
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq69282
    | exact resolve eq69282 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq69282
  have eq69472 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq69448 eq27
    | exact resolve eq27 eq69448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq69448
  have eq69729 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq69472 eq87
    | exact resolve eq87 eq69472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq69472
  have eq69814 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq69729
       have i₂ := eq69281
       grind)
    | exact superpose eq69281 eq69729
    | exact resolve eq69729 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69281 eq69729
  have eq69826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69814 eq15
    | exact resolve eq15 eq69814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69814
  have eq69874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq69826
    | exact resolve eq69826 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq69826
  have eq69883 : False := by grind
  exact eq69883

/-- `Equation4595`: `(x ◇ x) ◇ x = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pyx_Equation4595 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4595 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4595.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X2) X2) := by
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
  have eq174 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X4) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq16 x X3 X4
       have i₂ := eq16 x X0 X1
       grind)
    | (have i₁ := eq16 x X1 x
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op x y) y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 x X1 X2
       have i₂ := eq176 x
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1) X1
       have i₂ := eq176 X1
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq186 x X1
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq186
    | exact resolve eq186 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq191 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq176 x
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq194 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1) X1
       have i₂ := eq177 X1
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X1
    first
    | (have i₁ := eq194 x X1
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq194
    | exact resolve eq194 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq194
  have eq198 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | exact superpose eq191 eq195
    | exact resolve eq195 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq226 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq187 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq233 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq226 X0
       grind)
    | (have r₁ := eq226 X0
       have r₂ := eq191
       grind)
    | exact resolve eq226 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq351 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq198 (M.op sF0 y)
       have i₂ := eq233 (M.op sF0 y)
       grind)
    | exact superpose eq233 eq198
    | exact resolve eq198 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq534 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq233 eq456
    | exact resolve eq456 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq233 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq233
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq233 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq1081 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1087 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1054 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq2193 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1069
       grind)
    | exact superpose eq1069 eq39
    | exact resolve eq39 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq2194 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2193
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2193
    | exact resolve eq2193 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2196 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2194
    | exact resolve eq2194 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq16670 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq233 (M.op sF0 y)
       have i₂ := eq1087 (M.op sF0 y)
       grind)
    | exact superpose eq1087 eq233
    | (have j1 := eq1087 X0
       grind)
    | exact resolve eq233 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq16787 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq16670 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq16670 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq16670 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16670
  have eq16908 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq184 X0 X0
       have i₂ := eq16787 X0
       grind)
    | exact superpose eq16787 eq184
    | exact resolve eq184 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16914 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq534 X0
       have i₂ := eq16787 (σ X0)
       grind)
    | exact superpose eq16787 eq534
    | exact resolve eq534 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq16929 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16914 X0
       have i₂ := eq456 X0 (σ X0)
       grind)
    | exact superpose eq456 eq16914
    | exact resolve eq16914 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16914
  have eq16950 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq16929 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq16929
    | exact resolve eq16929 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16929
  have eq17321 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16908 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq16908
    | exact resolve eq16908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19544 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq351 eq17321
    | exact resolve eq17321 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19712 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq19544
       have i₂ := eq233 (σ (M.op sF0 y))
       grind)
    | exact superpose eq233 eq19544
    | exact resolve eq19544 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq19544
  have eq24090 : (τ (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq19712 eq456
    | exact resolve eq456 eq19712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq19712
  have eq24097 : (k (M.op (M.op x y) y) (M.op (M.op x y) y)) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq16950 eq24090
    | exact resolve eq24090 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16950 eq24090
  have eq24099 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq351 eq24097
    | exact resolve eq24097 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq24097
  have eq24115 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq24099 eq14
    | exact resolve eq14 eq24099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24099
  have eq32013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2196 eq1081
    | exact resolve eq1081 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq2196
  have eq32020 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq32013
       have r₂ := eq27
       grind)
    | exact resolve eq32013 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32013
  have eq32026 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32020
       have i₂ := eq16787 sF3
       grind)
    | exact superpose eq16787 eq32020
    | exact resolve eq32020 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32020
  have eq32030 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32026
       have i₂ := eq16787 sF2
       grind)
    | exact superpose eq16787 eq32026
    | exact resolve eq32026 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32026
  have eq32034 : x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32030
       have i₂ := eq16787 y
       grind)
    | exact superpose eq16787 eq32030
    | exact resolve eq32030 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32030
  have eq32036 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq32034
       have i₂ := eq16787 x
       grind)
    | exact superpose eq16787 eq32034
    | exact resolve eq32034 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32034
  have eq32286 : (τ (σ x)) = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq32036 eq115
    | exact resolve eq115 eq32036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq32036
  have eq32315 : x = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq32286
    | exact resolve eq32286 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32286
  have eq32316 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by grind
  clear eq32315
  have eq32334 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq32316 eq141
    | exact resolve eq141 eq32316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq32316
  have eq32366 : x = (k x x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq32334
    | exact resolve eq32334 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32334
  have eq32367 : x = (k y y) ∨ x = (k x x) := by grind
  clear eq32366
  have eq32400 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16908 y
       have i₂ := eq32367
       grind)
    | exact superpose eq32367 eq16908
    | exact resolve eq16908 eq32367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32401 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq17321 y
       have i₂ := eq32367
       grind)
    | exact superpose eq32367 eq17321
    | exact resolve eq17321 eq32367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32367
  have eq32406 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq32401
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32401
    | exact resolve eq32401 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq32401
  have eq32407 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq32400
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32400
    | exact resolve eq32400 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32400
  have eq32420 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq32406
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32406
    | exact resolve eq32406 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32406
  have eq32429 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (k x x) := by
    first
    | exact superpose eq26 eq32420
    | exact resolve eq32420 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32420
  have eq32434 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32407 eq32429
    | exact resolve eq32429 eq32407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32429
  have eq32449 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq32434
       grind)
    | exact superpose eq32434 eq39
    | exact resolve eq39 eq32434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32459 : (M.op (M.op x y) y) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16908 x
       have i₂ := eq32434
       grind)
    | exact superpose eq32434 eq16908
    | exact resolve eq16908 eq32434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32460 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17321 x
       have i₂ := eq32434
       grind)
    | exact superpose eq32434 eq17321
    | exact resolve eq17321 eq32434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32471 : (M.op (M.op x y) y) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32460
       have i₂ := eq16787 (σ x)
       grind)
    | exact superpose eq16787 eq32460
    | exact resolve eq32460 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32460
  have eq32472 : (k x x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32459
       have i₂ := eq16787 x
       grind)
    | exact superpose eq16787 eq32459
    | exact resolve eq32459 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32459
  have eq32480 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32449
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32449
    | exact resolve eq32449 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32449
  have eq32487 : (σ (k x x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32471
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq32471
    | exact resolve eq32471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32471
  have eq32488 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32434 eq32472
    | exact resolve eq32472 eq32434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32434 eq32472
  have eq32497 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32487
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq32487
    | exact resolve eq32487 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32487
  have eq32503 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32497
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32497
    | exact resolve eq32497 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32497
  have eq32508 : x = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32488 eq32503
    | exact resolve eq32503 eq32488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32503
  have eq32512 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq32480 eq32508
    | exact resolve eq32508 eq32480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32508
  have eq32977 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32480 eq16908
    | exact resolve eq16908 eq32480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32990 : (k (σ x) (σ x)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32977
       have i₂ := eq16787 sF2
       grind)
    | exact superpose eq16787 eq32977
    | exact resolve eq32977 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32977
  have eq33008 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32480 eq32990
    | exact resolve eq32990 eq32480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32480 eq32990
  have eq33032 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32488 eq198
    | exact resolve eq198 eq32488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq33117 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X1) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq32488 eq174
    | exact resolve eq174 eq32488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32488
  have eq33122 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33117 x x
       have i₂ := eq184 x x
       grind)
    | (have i₁ := eq33117 x y
       have i₂ := eq184 x x
       grind)
    | exact superpose eq184 eq33117
    | (have j0 := eq33117 x y
       grind)
    | exact resolve eq33117 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33117
  have eq33202 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32512 eq33032
    | exact resolve eq33032 eq32512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32512 eq33032
  have eq33206 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33122
    | exact resolve eq33122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33122
  have eq33537 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33202 eq26
    | (have j1 := eq33202 (σ y)
       grind)
    | exact resolve eq26 eq33202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq33202
  have eq33593 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq33537
  have eq33684 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33206 eq33008
    | exact resolve eq33008 eq33206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33008 eq33206
  have eq33691 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq33684
  have eq33697 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33691
       have r₂ := eq33593
       grind)
    | exact resolve eq33691 eq33593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33593 eq33691
  have eq33761 : (M.op (M.op x y) y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq33697 eq191
    | exact resolve eq191 eq33697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq33762 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq33697 eq27
    | exact resolve eq27 eq33697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq33697
  have eq33900 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op x y) (σ y)) y) := by
    intro X0 X1
    first
    | exact superpose eq33761 eq174
    | exact resolve eq174 eq33761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq33901 : (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) y) := by
    first
    | exact superpose eq33761 eq184
    | exact resolve eq184 eq33761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33904 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq33901 eq33900
    | exact resolve eq33900 eq33901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33900 eq33901
  have eq36228 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (M.op x y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33904 X0 X0
       have i₂ := eq16787 X0
       grind)
    | exact superpose eq16787 eq33904
    | exact resolve eq33904 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33904
  have eq36602 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq32407 eq24115
    | exact resolve eq24115 eq32407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24115 eq32407
  have eq36625 : (M.op x y) = (σ (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq36602
    | exact resolve eq36602 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36602
  have eq36681 : x = (k x x) := by
    first
    | (have r₁ := eq36625
       have r₂ := eq33762
       grind)
    | exact resolve eq36625 eq33762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36625
  have eq36711 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq36681
       grind)
    | exact superpose eq36681 eq39
    | exact resolve eq39 eq36681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36721 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq16908 x
       have i₂ := eq36681
       grind)
    | exact superpose eq36681 eq16908
    | exact resolve eq16908 eq36681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16908
  have eq36722 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17321 x
       have i₂ := eq36681
       grind)
    | exact superpose eq36681 eq17321
    | exact resolve eq17321 eq36681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17321
  have eq36726 : (M.op x x) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq36228 x
       have i₂ := eq36681
       grind)
    | exact superpose eq36681 eq36228
    | exact resolve eq36228 eq36681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36228
  have eq36731 : (k x x) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq36726
       have i₂ := eq16787 x
       grind)
    | exact superpose eq16787 eq36726
    | exact resolve eq36726 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36726
  have eq36735 : (M.op (M.op x y) y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36722
       have i₂ := eq16787 (σ x)
       grind)
    | exact superpose eq16787 eq36722
    | exact resolve eq36722 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36722
  have eq36736 : (k x x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq36721
       have i₂ := eq16787 x
       grind)
    | exact superpose eq16787 eq36721
    | exact resolve eq36721 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16787 eq36721
  have eq36743 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36711
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36711
    | exact resolve eq36711 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36711
  have eq36747 : x = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq36731
       have i₂ := eq36681
       grind)
    | exact superpose eq36681 eq36731
    | exact resolve eq36731 eq36681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36731
  have eq36751 : (σ (k x x)) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq36735
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq36735
    | exact resolve eq36735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36735
  have eq36752 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq36736
       have i₂ := eq36681
       grind)
    | exact superpose eq36681 eq36736
    | exact resolve eq36736 eq36681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36681 eq36736
  have eq36760 : (σ (k x x)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq33761 eq36751
    | exact resolve eq36751 eq33761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33761 eq36751
  have eq36767 : x = (σ (k x x)) := by
    first
    | exact superpose eq36747 eq36760
    | exact resolve eq36760 eq36747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36747 eq36760
  have eq36772 : x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36767
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq36767
    | exact resolve eq36767 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq36767
  have eq36776 : x = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36772
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36772
    | exact resolve eq36772 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36772
  have eq36779 : x = (σ x) := by
    first
    | exact superpose eq36743 eq36776
    | exact resolve eq36776 eq36743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36743 eq36776
  have eq37915 : x = (M.op x y) := by
    first
    | exact superpose eq36752 eq184
    | exact resolve eq184 eq36752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq36752
  have eq37918 : x = (M.op x y) := by
    first
    | (have i₁ := eq37915
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37915
    | exact resolve eq37915 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq37915
  have eq38107 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq37918
       grind)
    | exact superpose eq37918 eq22
    | exact resolve eq22 eq37918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq38141 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq36779
       have i₂ := eq37918
       grind)
    | exact superpose eq37918 eq36779
    | exact resolve eq36779 eq37918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36779 eq37918
  have eq38163 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38141 eq38107
    | exact resolve eq38107 eq38141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38107 eq38141
  have eq38555 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq38163 eq20
    | exact resolve eq20 eq38163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq38163
  have eq38715 : False := by grind
  exact eq38715

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_y_pyx_y_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X2 X0 X2
       have i₂ := eq14 X0 X2 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X2) X0
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X3) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op (M.op (M.op X0 X0) X1) X0) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 X0) = (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (M.op X2 X2) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X2 X2)
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X2) (M.op X1 X2))
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq89
    | (have j0 := eq89 (σ X0) (σ X1)
       grind)
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq89 y x
       grind)
    | exact superpose eq89 eq95
    | (have j1 := eq89 y x
       grind)
    | exact resolve eq95 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq127
    | exact resolve eq127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq129
    | exact resolve eq129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq89
    | (have j0 := eq89 (σ y) (σ x)
       grind)
    | exact resolve eq89 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq199
    | exact resolve eq199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq203 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq200
       have r₂ := eq27
       grind)
    | exact resolve eq200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq203
    | exact resolve eq203 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq207 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq27
    | exact resolve eq27 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq53 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq54 eq259
    | exact resolve eq259 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : (M.op (M.op x y) (σ x)) = (M.op (σ x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq429
    | exact resolve eq429 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq450 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X2 X2) X0 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X2) X0 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 X0) x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq519 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op x y) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq447 eq14
    | exact resolve eq14 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq520 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54 eq519
    | exact resolve eq519 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq519
  have eq521 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq520 x
       have i₂ := eq51 sF0 sF2 x x
       grind)
    | (have i₁ := eq520 x
       have i₂ := eq51 sF0 X1 x sF2
       grind)
    | exact superpose eq51 eq520
    | exact resolve eq520 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq614 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op X3 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 X4 X2 X0
       have i₂ := eq51 X0 X0 (M.op X2 X2) X1
       grind)
    | (have i₁ := eq55 X3 X4 X2 X0
       have i₂ := eq51 X0 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X4 X2 X0 X3
       have i₂ := eq51 X0 X0 (M.op X2 X3) X1
       grind)
    | (have i₁ := eq56 X4 X2 X0 X3
       have i₂ := eq51 X0 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq56
  have eq1133 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1356 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) ≠ (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X2 X2) (M.op X2 X2))) ∨ (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X3) = (k X3 (M.op (M.op X2 X2) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68 (M.op X2 X2) (M.op (M.op X2 X2) (M.op X2 X2)) X3
       have i₂ := eq55 X0 X1 X2 (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact superpose eq55 eq68
    | (have j0 := eq68 (M.op X2 X2) X1 X3
       grind)
    | (have r₁ := eq68 X2 X2 (M.op X2 X2)
       have r₂ := eq55 X2 X2 X2 X2
       grind)
    | exact resolve eq68 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq68
  have eq1486 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq11472 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq450 X0 X1 X2 X3 x
       have i₂ := eq454 X2 X3 x
       grind)
    | exact superpose eq454 eq450
    | exact resolve eq450 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq454
  have eq13827 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X2) X0) = (M.op (M.op X0 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq614 X0 X1 X2 x x
       have i₂ := eq11472 x x X2 X0
       grind)
    | (have i₁ := eq614 x X1 X2 x y
       have i₂ := eq11472 X0 X1 X2 x
       grind)
    | exact superpose eq11472 eq614
    | (have j0 := eq614 X0 X1 X2 x y
       grind)
    | exact resolve eq614 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq15436 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) X2) X0) = (M.op (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq753 X0 X1 X2 X3 x
       have i₂ := eq11472 x x X2 X0
       grind)
    | exact superpose eq11472 eq753
    | exact resolve eq753 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq77975 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) ≠ (M.op (M.op (M.op x y) (M.op X2 X2)) (M.op X0 X1)) ∨ (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X3) = (k X3 (M.op (M.op X2 X2) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1356 X0 X1 X2 X3
       have i₂ := eq13827 (M.op X0 X1) X2 (M.op X2 X2)
       grind)
    | exact superpose eq13827 eq1356
    | (have j0 := eq1356 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1356 (M.op x y) (M.op X1 X1) X1 (M.op (M.op x y) (M.op X1 X1))
       have r₂ := eq13827 (M.op (M.op x y) (M.op X1 X1)) X1 (M.op X1 X1)
       grind)
    | exact resolve eq1356 eq13827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq77976 : ∀ X0 X2 X3 : G, (M.op X3 X3) ≠ (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (M.op (M.op (M.op X2 X2) (M.op X2 X2)) X3) = (k X3 (M.op (M.op X2 X2) (M.op X2 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq77975 X2 X3 X2 X3
       have i₂ := eq15436 sF0 (M.op X2 X2) X2 X3
       grind)
    | exact superpose eq15436 eq77975
    | (have j0 := eq77975 X0 x X2 X3
       grind)
    | (have r₁ := eq77975 X2 X2 X2 (M.op (M.op X2 X2) X3)
       have r₂ := eq15436 (M.op X2 X2) X3 (M.op X2 X2) X3
       grind)
    | exact resolve eq77975 eq15436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77975
  have eq77977 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (M.op x y) X2) X2) X3) = (k X3 (M.op (M.op (M.op x y) X2) X2)) ∨ (M.op X3 X3) ≠ (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq77976 X0 X2 X3
       have i₂ := eq13827 X2 X2 X2
       grind)
    | exact superpose eq13827 eq77976
    | (have j0 := eq77976 X0 X2 X3
       grind)
    | (have r₁ := eq77976 (M.op x y) X2 (M.op (M.op x y) (M.op x y))
       have r₂ := eq13827 (M.op x y) (M.op x y) (M.op x y)
       grind)
    | exact resolve eq77976 eq13827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77976
  have eq77978 : ∀ X0 X2 X3 : G, (M.op X3 X3) ≠ (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (M.op (M.op (M.op x y) X2) X3) = (k X3 (M.op (M.op (M.op x y) X2) X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq77977 X0 X2 X3
       have i₂ := eq11472 sF0 X2 X2 X3
       grind)
    | exact superpose eq11472 eq77977
    | (have j0 := eq77977 X0 X2 X3
       grind)
    | exact resolve eq77977 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11472 eq77977
  have eq78538 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1486 X0 X1
       have i₂ := eq13827 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq13827 eq1486
    | (have j0 := eq1486 X0 X1
       grind)
    | exact resolve eq1486 eq13827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486 eq13827
  have eq78539 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq78538 x x
       have i₂ := eq15436 sF0 (M.op x x) x x
       grind)
    | exact superpose eq15436 eq78538
    | (have j0 := eq78538 X0 X1
       grind)
    | exact resolve eq78538 eq15436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78538
  have eq78540 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (k X0 (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op X0 X0) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq78539 (M.op x y) x
       have i₂ := eq15436 (M.op (M.op x y) x) x x x
       grind)
    | (have i₁ := eq78539 x x
       have i₂ := eq15436 x x x x
       grind)
    | exact superpose eq15436 eq78539
    | (have j0 := eq78539 X0 x
       grind)
    | exact resolve eq78539 eq15436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15436 eq78539
  have eq78541 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (k X0 (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have j0 := eq78540 X0
       have j1 := eq77978 X0 X0 X0
       grind)
    | (have r₁ := eq78540 X0
       have r₂ := eq77978 X0 x X0
       grind)
    | exact resolve eq78540 eq77978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77978 eq78540
  have eq78757 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq521 eq78541
    | exact resolve eq78541 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq78896 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq205 eq78757
    | exact resolve eq78757 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78757
  have eq79183 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq78896 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78896
  have eq79384 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq79183
    | (have j0 := eq79183 (σ y)
       grind)
    | exact resolve eq79183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79183
  have eq79562 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq79384
    | exact resolve eq79384 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq79384
  have eq79573 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq79562
  have eq80015 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79573 eq130
    | exact resolve eq130 eq79573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq79573
  have eq80025 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq80015
  have eq80030 : x = (M.op x y) := by
    first
    | (have r₁ := eq80025
       have r₂ := eq207
       grind)
    | exact resolve eq80025 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq80025
  have eq80033 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq80030 eq20
    | exact resolve eq20 eq80030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq80076 : ∀ X0 : G, (M.op (M.op x X0) X0) = (k X0 (M.op (M.op x X0) X0)) := by
    intro X0
    first
    | exact superpose eq80030 eq78541
    | exact resolve eq78541 eq80030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78541
  have eq80080 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq80076 x
       have i₂ := eq259 x x
       grind)
    | (have i₁ := eq80076 y
       have i₂ := eq259 X0 y
       grind)
    | exact superpose eq259 eq80076
    | exact resolve eq80076 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq80076
  have eq80115 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq80033
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq80033
    | exact resolve eq80033 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80033
  have eq80117 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq80030 eq80080
    | exact resolve eq80080 eq80030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80080
  have eq81023 : (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq80117 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80117
    | (have j0 := eq80117 y
       grind)
    | exact resolve eq80117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq80117
  have eq81057 : x = (k y x) := by
    first
    | exact superpose eq80030 eq81023
    | exact resolve eq81023 eq80030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80030 eq81023
  have eq81073 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1133 x y
       have i₂ := eq81057
       grind)
    | exact superpose eq81057 eq1133
    | (have j0 := eq1133 x y
       grind)
    | exact resolve eq1133 eq81057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq81057
  have eq81077 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq81073
  have eq81085 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81077
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq81077
    | exact resolve eq81077 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq81077
  have eq81093 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81085
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81085
    | exact resolve eq81085 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq81085
  have eq81099 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq81093
    | exact resolve eq81093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq81093
  have eq81105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq80115 eq81099
    | exact resolve eq81099 eq80115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80115 eq81099
  have eq81110 : False := by grind
  exact eq81110

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyx_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq70 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq70 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq266 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq271 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       have j1 := eq74 X1 X0
       grind)
    | (have r₁ := eq266 X1 X1
       have r₂ := eq74 X1 X1
       grind)
    | (have r₁ := eq266 X1 X0
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq266 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq266
  have eq367 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq271 (σ X1) (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1
       have i₂ := eq271 X1 X0
       grind)
    | exact superpose eq271 eq367
    | exact resolve eq367 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq367
  have eq374 : False := by grind
  exact eq374

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_pyy_pyx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq83 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq74 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq74 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq74 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq286 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq83 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq293 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq286 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq286 X1 X1
       have r₂ := eq78 X1 X1
       grind)
    | exact resolve eq286 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq286
  have eq568 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq293 (σ X1) (σ X0)
       grind)
    | exact superpose eq293 eq15
    | exact resolve eq15 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1
       have i₂ := eq293 X1 X0
       grind)
    | exact superpose eq293 eq568
    | exact resolve eq568 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq568
  have eq578 : False := by grind
  exact eq578

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_y_pyx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X2) X0
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X1 X3) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X2 X2) X0 X3 X4
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq62 (M.op X1 X2) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X4) X3) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X1 X2) X0 X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq62 (M.op X0 X0) X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X2 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq62 X1 X2 X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq123 (σ X0)
       grind)
    | exact superpose eq123 eq15
    | exact resolve eq15 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq123 (τ X0)
       grind)
    | exact superpose eq123 eq18
    | exact resolve eq18 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq133 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq130 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq130
    | exact resolve eq130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq126 X0
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq126
    | exact resolve eq126 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq141 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq123 X0
       grind)
    | exact superpose eq123 eq133
    | exact resolve eq133 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq133
  have eq148 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 X2 (σ X0) (σ X0)
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq71
    | exact resolve eq71 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ X0) X1 X2 (σ X0)
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq62
    | exact resolve eq62 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq141 X0
       grind)
    | exact superpose eq141 eq10
    | exact resolve eq10 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq173 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X1) X2) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (τ X0) X1 X2 (τ X0)
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq62
    | exact resolve eq62 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X3 X3)) (M.op X1 X2)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq148 X3 (M.op X1 X2) (σ X0)
       have i₂ := eq148 X0 X1 X2
       grind)
    | exact superpose eq148 eq148
    | exact resolve eq148 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (σ (M.op X0 X0)) X1
       have i₂ := eq137 (M.op X0 X0)
       grind)
    | exact superpose eq137 eq148
    | exact resolve eq148 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (τ X0)) X1) X2) = (M.op (τ (τ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 (τ X0) X1 X2
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq173
    | exact resolve eq173 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq431 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X4 X5) X2) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq64 X4 X5 X2 X3
       have i₂ := eq64 X0 X1 X2 X3
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq537 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X2 X2) X3)) = (M.op (M.op (M.op X4 X4) X0) (M.op X2 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65 X4 X0 (M.op X2 X2) X1
       have i₂ := eq65 X2 (M.op X2 X2) (M.op X0 X1) X3
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq785 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X4) X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 X2 X3 X4 X0 X5
       have i₂ := eq71 (M.op X2 X3) X4 X0 X1
       grind)
    | (have i₁ := eq67 X2 X3 X4 X0 X5
       have i₂ := eq71 X0 X1 (M.op X2 X3) X4
       grind)
    | exact superpose eq71 eq67
    | exact resolve eq67 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1163 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X4 X5) X6) X3) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq70 X6 X0 X1 X3 X2
       have i₂ := eq67 X4 X5 X6 X3 X0
       grind)
    | (have i₁ := eq70 X1 X2 X2 X3 X4
       have i₂ := eq67 X1 X1 X2 X3 X4
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq70
  have eq1784 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X5 X6) X4) X0) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq431 X2 X3 X4 X0 X5 X6
       have i₂ := eq71 (M.op X2 X3) X4 X0 X1
       grind)
    | (have i₁ := eq431 X2 X3 X4 X0 X5 X6
       have i₂ := eq71 X0 X1 (M.op X2 X3) X4
       grind)
    | exact superpose eq71 eq431
    | exact resolve eq431 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq2514 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2515 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2514 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2514
    | (have j0 := eq2514 (σ X0) (σ X1)
       grind)
    | exact resolve eq2514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4764 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2515 X1 X0
       have i₂ := eq2514 X1 X0
       grind)
    | exact superpose eq2514 eq2515
    | (have j0 := eq2515 X1 X0
       have j1 := eq2514 (σ X1) (σ X0)
       grind)
    | exact resolve eq2515 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514 eq2515
  have eq5639 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X2) (M.op X3 X4)) = (M.op (M.op (σ (M.op X0 X0)) X5) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq785 X1 X2 X3 X4 (σ X0) X5
       have i₂ := eq137 X0
       grind)
    | exact superpose eq137 eq785
    | exact resolve eq785 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq30806 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4764 x y
       grind)
    | exact superpose eq4764 eq16
    | (have j1 := eq4764 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq4764 x y
       grind)
    | exact resolve eq16 eq4764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4764
  have eq30913 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30806
  have eq30976 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq150 x (σ y) X0
       have i₂ := eq30913
       grind)
    | exact superpose eq30913 eq150
    | exact resolve eq150 eq30913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq30978 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X1) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ x) (σ y) X0 X1
       have i₂ := eq30913
       grind)
    | exact superpose eq30913 eq62
    | exact resolve eq62 eq30913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30980 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X0 X1) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ x) (σ y) X0 X1
       have i₂ := eq30913
       grind)
    | exact superpose eq30913 eq71
    | exact resolve eq71 eq30913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq31477 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30980 (σ (M.op x x)) X0
       have i₂ := eq30976 X0
       grind)
    | exact superpose eq30976 eq30980
    | exact resolve eq30980 eq30976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31622 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31477
  have eq31647 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30980 eq31622
    | exact resolve eq31622 eq30980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31622
  have eq31658 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31647
       have i₂ := eq137 x
       grind)
    | exact superpose eq137 eq31647
    | exact resolve eq31647 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31647
  have eq116103 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 X0 X1
       have i₂ := eq183 X0 X1 X2 X0
       grind)
    | exact superpose eq183 eq201
    | exact resolve eq201 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq116105 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq201 X0 x
       have i₂ := eq5639 X0 (σ X0) X1 X2 X3 x
       grind)
    | exact superpose eq5639 eq201
    | exact resolve eq201 eq5639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116708 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (σ (M.op X3 X3)) (M.op X4 X5)) = (σ (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq116103 X3 X4 X5
       have i₂ := eq1784 X3 X3 X3 X3 X2 X0 X1
       grind)
    | (have i₁ := eq116103 (M.op X5 x) X1 X2
       have i₂ := eq1784 (M.op (M.op X5 x) (M.op X5 x)) X1 X2 X3 (M.op X5 x) X5 x
       grind)
    | exact superpose eq1784 eq116103
    | exact resolve eq116103 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116740 : ∀ X0 X1 X2 : G, (σ (M.op (τ (τ (M.op X0 X0))) (M.op (τ (τ X0)) (τ (τ X0))))) = (M.op (σ (M.op (τ (τ X0)) (τ (τ X0)))) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116103 (τ (τ X0)) X1 X2
       have i₂ := eq355 X0 (τ (τ X0)) (M.op (τ (τ X0)) (τ (τ X0)))
       grind)
    | exact superpose eq355 eq116103
    | exact resolve eq116103 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq116103
  have eq117227 : ∀ X0 X1 X2 : G, (σ (M.op (τ (τ (M.op X0 X0))) (τ (M.op (τ X0) (τ X0))))) = (M.op (σ (τ (M.op (τ X0) (τ X0)))) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116740 X0 X1 X2
       have i₂ := eq163 (τ X0)
       grind)
    | exact superpose eq163 eq116740
    | exact resolve eq116740 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116740
  have eq117263 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) (τ X0)) (M.op X1 X2)) = (σ (M.op (τ (τ (M.op X0 X0))) (τ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117227 X0 X1 X2
       have i₂ := eq11 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq11 eq117227
    | exact resolve eq117227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117227
  have eq117288 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) (M.op X1 X2)) = (σ (M.op (τ (τ (M.op X0 X0))) (τ (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117263 X0 X1 X2
       have i₂ := eq163 X0
       grind)
    | exact superpose eq163 eq117263
    | exact resolve eq117263 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117263
  have eq117298 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) (M.op X1 X2)) = (σ (τ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117288 X0 X1 X2
       have i₂ := eq163 (τ (M.op X0 X0))
       grind)
    | exact superpose eq163 eq117288
    | exact resolve eq117288 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117288
  have eq117308 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117298 X0 X1 X2
       have i₂ := eq11 (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))
       grind)
    | exact superpose eq11 eq117298
    | exact resolve eq117298 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117298
  have eq117314 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117308 X0 X1 X2
       have i₂ := eq163 (M.op X0 X0)
       grind)
    | exact superpose eq163 eq117308
    | exact resolve eq117308 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq117308
  have eq123708 : ∀ X0 X1 : G, (M.op (τ (M.op (σ x) (σ x))) (M.op X0 X1)) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq117314 (σ x) X0 X1
       have i₂ := eq30978 (M.op (σ x) (σ x)) (σ x)
       grind)
    | exact superpose eq30978 eq117314
    | exact resolve eq117314 eq30978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30978 eq117314
  have eq124264 : ∀ X0 X1 : G, (τ (M.op (σ x) (σ (M.op x x)))) = (M.op (τ (σ (M.op x x))) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq123708 X0 X1
       have i₂ := eq137 x
       grind)
    | exact superpose eq137 eq123708
    | exact resolve eq123708 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq123708
  have eq124301 : ∀ X0 X1 : G, (τ (M.op (σ x) (σ (M.op x x)))) = (M.op (M.op x x) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq124264 X0 X1
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq124264
    | exact resolve eq124264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124264
  have eq124324 : ∀ X0 X1 : G, (τ (σ (M.op x x))) = (M.op (M.op x x) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq31658 eq124301
    | exact resolve eq124301 eq31658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31658 eq124301
  have eq124336 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x x) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq124324 X0 X1
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq124324
    | exact resolve eq124324 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124324
  have eq124469 : (M.op x x) = (M.op (M.op x x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124336 (σ x) (σ y)
       have i₂ := eq30913
       grind)
    | exact superpose eq30913 eq124336
    | exact resolve eq124336 eq30913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124805 : (M.op x x) = (M.op (M.op x x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq124469
  have eq124896 : (M.op x x) = (M.op (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30980 x x
       have i₂ := eq124805
       grind)
    | exact superpose eq124805 eq30980
    | exact resolve eq30980 eq124805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30980 eq124805
  have eq125048 : (M.op x x) = (M.op (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq124896
  have eq125110 : ∀ X0 X1 : G, (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op x x) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq116105 x x X0 X1
       have i₂ := eq125048
       grind)
    | exact superpose eq125048 eq116105
    | exact resolve eq116105 eq125048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116105 eq125048
  have eq125265 : (M.op x x) = (σ (M.op (M.op x x) (M.op x x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124336 eq125110
    | exact resolve eq125110 eq124336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125110
  have eq125273 : (M.op x x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124336 eq125265
    | exact resolve eq125265 eq124336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124336 eq125265
  have eq125281 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op x x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq125273 eq30976
    | exact resolve eq30976 eq125273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30976 eq125273
  have eq125582 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op x X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq125281 X1
       have i₂ := eq62 x x X1 X0
       grind)
    | (have i₁ := eq125281 X1
       have i₂ := eq62 x X0 X1 x
       grind)
    | exact superpose eq62 eq125281
    | exact resolve eq125281 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125281
  have eq127647 : ∀ X0 : G, (σ x) = (M.op (M.op x X0) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30913
       have i₂ := eq125582 X0 (σ y)
       grind)
    | exact superpose eq125582 eq30913
    | exact resolve eq30913 eq125582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125582
  have eq128220 : ∀ X0 : G, (σ x) = (M.op (M.op x X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq127647 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127647
  have eq128804 : (σ x) = (M.op (σ (M.op y y)) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128220 x
       have i₂ := eq148 y x x
       grind)
    | exact superpose eq148 eq128220
    | exact resolve eq128220 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128220
  have eq129038 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) (M.op y y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq201 y x
       have i₂ := eq128804
       grind)
    | exact superpose eq128804 eq201
    | exact resolve eq201 eq128804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128804
  have eq129194 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30913 eq129038
    | exact resolve eq129038 eq30913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30913 eq129038
  have eq137368 : (τ (σ x)) = (M.op (M.op y y) (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op (M.op y y) (M.op y y))
       have i₂ := eq129194
       grind)
    | exact superpose eq129194 eq10
    | exact resolve eq10 eq129194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129194
  have eq137429 : x = (M.op (M.op y y) (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137368
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq137368
    | exact resolve eq137368 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137368
  have eq137450 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op X0 X1) X2) y) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137429
       have i₂ := eq1784 y y y y X2 X0 X1
       grind)
    | exact superpose eq1784 eq137429
    | exact resolve eq137429 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1784
  have eq138246 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137450 y y (M.op y y)
       have i₂ := eq137429
       grind)
    | exact superpose eq137429 eq137450
    | exact resolve eq137450 eq137429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137429 eq137450
  have eq138446 : x = (M.op x y) := by grind
  clear eq138246
  have eq138567 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138446
       grind)
    | exact superpose eq138446 eq16
    | exact resolve eq16 eq138446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138569 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 x y X0 X1
       have i₂ := eq138446
       grind)
    | exact superpose eq138446 eq62
    | exact resolve eq62 eq138446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq138576 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) x) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq148 X0 x y
       have i₂ := eq138446
       grind)
    | exact superpose eq138446 eq148
    | exact resolve eq148 eq138446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq141337 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X3 X4)) = (M.op (M.op x (σ X0)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5639 X0 X1 X2 X3 X4 x
       have i₂ := eq138576 X0
       grind)
    | exact superpose eq138576 eq5639
    | exact resolve eq5639 eq138576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5639 eq138576
  have eq141523 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X3 X4)) = (M.op x X1) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq141337 x X1 X2 X3 X4
       have i₂ := eq138569 X1 (σ x)
       grind)
    | exact superpose eq138569 eq141337
    | exact resolve eq141337 eq138569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141337
  have eq143669 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X4 X4) X0) (M.op X2 X2)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq537 X0 X1 X2 x X4
       have i₂ := eq141523 (M.op X0 X1) (M.op X0 X1) (M.op X2 X2) x
       grind)
    | exact superpose eq141523 eq537
    | exact resolve eq537 eq141523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq145428 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X3) X4) X5) = (M.op (M.op x (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1163 X2 X3 X4 X5 (M.op x x) X0 (M.op x x)
       have i₂ := eq143669 X0 X1 x x
       grind)
    | exact superpose eq143669 eq1163
    | exact resolve eq1163 eq143669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163 eq143669
  have eq145972 : ∀ X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X3) X4) X5) = (M.op x X5) := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq145428 x x X2 X3 X4 X5
       have i₂ := eq138569 X5 (M.op x x)
       grind)
    | exact superpose eq138569 eq145428
    | exact resolve eq145428 eq138569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138569 eq145428
  have eq156712 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op X0 X1) X2) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq145972 X0 X1 X2 y
       have i₂ := eq138446
       grind)
    | exact superpose eq138446 eq145972
    | exact resolve eq145972 eq138446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145972
  have eq158473 : ∀ X0 X1 : G, (σ x) = (M.op (σ (M.op y y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq116708 x x x y X0 X1
       have i₂ := eq156712 x x x
       grind)
    | exact superpose eq156712 eq116708
    | exact resolve eq116708 eq156712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116708 eq156712
  have eq190031 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq201 y (M.op x x)
       have i₂ := eq158473 x x
       grind)
    | exact superpose eq158473 eq201
    | exact resolve eq201 eq158473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq158473
  have eq190280 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq190031
       have i₂ := eq141523 y y y y
       grind)
    | exact superpose eq141523 eq190031
    | exact resolve eq190031 eq141523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141523 eq190031
  have eq190333 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq190280
       have i₂ := eq138446
       grind)
    | exact superpose eq138446 eq190280
    | exact resolve eq190280 eq138446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138446 eq190280
  have eq190346 : False := by grind
  exact eq190346
