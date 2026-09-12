import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1663`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxy_x_pyx_Equation1663 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1663 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1663.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) = X0 := by
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
  have eq51 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X5)) = X1 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) (M.op (M.op X2 x) x) X5
       have i₂ := eq14 X0 X2 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x (M.op (M.op x x) x)
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq57 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 y x
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ y) (σ x)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 (M.op (M.op X1 X2) X3) (M.op X0 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq74 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k x y) := by
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
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq102 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq110 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq92
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y x) = (τ (k (σ y) (σ x))) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq117
    | exact resolve eq117 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq119
  have eq134 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq152 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq141 eq16
    | exact resolve eq16 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq167 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq143 eq16
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq187 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq124
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq187
  have eq211 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq167
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq167
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq167 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq213 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq211
  have eq232 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq57
    | exact resolve eq57 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op x y)) (M.op x X3)) = X0 := by
    intro X0 X3
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq238 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq57
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) X3)) = X0 := by
    intro X0 X3
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq400 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq233 (M.op X1 sF0) x
       have i₂ := eq57 sF0 X1
       grind)
    | exact superpose eq57 eq233
    | exact resolve eq233 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (k (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1
    grind
  have eq469 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq239 (M.op X1 sF4) x
       have i₂ := eq57 sF4 X1
       grind)
    | exact superpose eq57 eq239
    | exact resolve eq239 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X0 x) (M.op X0 X2)
       have i₂ := eq56 X0 (M.op X0 x) X2 x
       grind)
    | exact superpose eq56 eq70
    | exact resolve eq70 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq57
    | (have j1 := eq95 X0 X1
       grind)
    | exact resolve eq57 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq6677 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq686 X0 X1 X2
       have i₂ := eq60 (M.op X0 X1) X0 X1 (M.op X0 X2)
       grind)
    | exact superpose eq60 eq686
    | exact resolve eq686 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq686
  have eq6949 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq764 y y
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq764
    | (have j0 := eq764 y y
       grind)
    | exact resolve eq764 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq6951 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq134 eq764
    | (have j0 := eq764 (M.op x y) (τ X0)
       grind)
    | exact resolve eq764 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq7071 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6949
  have eq7097 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq6951
    | (have j0 := eq6951 X0
       grind)
    | exact resolve eq6951 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6951
  have eq7099 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7071
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq7071
    | exact resolve eq7071 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7071
  have eq7189 : ∀ X0 : G, (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq7097 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7097
    | (have j0 := eq7097 X0
       grind)
    | exact resolve eq7097 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7097
  have eq7191 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7099
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq7099
    | exact resolve eq7099 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7099
  have eq7277 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq7189 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7189
    | (have j0 := eq7189 X0
       grind)
    | exact resolve eq7189 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7189
  have eq7363 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq7277
    | (have j0 := eq7277 X0
       grind)
    | exact resolve eq7277 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7277
  have eq7445 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq7363
    | (have j0 := eq7363 X0
       grind)
    | exact resolve eq7363 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7363
  have eq7527 : ∀ X0 : G, (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7445 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7445
    | (have j0 := eq7445 X0
       grind)
    | exact resolve eq7445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7445
  have eq22699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq22708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq22699
    | exact resolve eq22699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22699
  have eq22719 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22708
       have r₂ := eq28
       grind)
    | exact resolve eq22708 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22708
  have eq22732 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22719 eq57
    | exact resolve eq57 eq22719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22719
  have eq22750 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq22732
    | exact resolve eq22732 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22732
  have eq22762 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22750 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq22750
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq22750
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq22750
       grind)
    | exact resolve eq12 eq22750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22750
  have eq22783 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq22762
  have eq27982 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22783 eq116
    | exact resolve eq116 eq22783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq22783
  have eq28014 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq27982
    | exact resolve eq27982 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27982
  have eq28017 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq28014
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq28014
       have r₂ := eq12 y x
       grind)
    | exact resolve eq28014 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28014
  have eq28040 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28017 eq57
    | exact resolve eq57 eq28017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28017
  have eq28066 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq28040
    | exact resolve eq28040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28040
  have eq28067 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq28066
  have eq28094 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq28067
       grind)
    | exact superpose eq28067 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq28067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28067
  have eq28105 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28094
  have eq28115 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28105
    | exact resolve eq28105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28105
  have eq28225 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57 y y
       have i₂ := eq28115
       grind)
    | exact superpose eq28115 eq57
    | exact resolve eq57 eq28115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28115
  have eq28243 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28225
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28225
    | exact resolve eq28225 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28225
  have eq28244 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28243
  have eq28255 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq232 x X0
       have i₂ := eq28244
       grind)
    | exact superpose eq28244 eq232
    | exact resolve eq232 eq28244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq28262 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op y X1)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 y X0 x X1
       have i₂ := eq28244
       grind)
    | exact superpose eq28244 eq56
    | exact resolve eq56 eq28244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28264 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq28244
       grind)
    | exact superpose eq28244 eq57
    | exact resolve eq57 eq28244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28266 : (M.op (M.op x y) x) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70 y x
       have i₂ := eq28244
       grind)
    | exact superpose eq28244 eq70
    | exact resolve eq70 eq28244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq28244
  have eq28282 : (M.op (M.op x y) x) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28266
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28266
    | exact resolve eq28266 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28266
  have eq28289 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28255 x
       have i₂ := eq400 x x
       grind)
    | (have i₁ := eq28255 y
       have i₂ := eq400 x x
       grind)
    | exact superpose eq400 eq28255
    | (have j0 := eq28255 y
       grind)
    | exact resolve eq28255 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq28255
  have eq28297 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq233 X0 x
       have i₂ := eq28264
       grind)
    | exact superpose eq28264 eq233
    | exact resolve eq233 eq28264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq28299 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq28330 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28299
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28299
    | exact resolve eq28299 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28299
  have eq28807 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28289 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq28289
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq28289
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq28289
       grind)
    | exact resolve eq12 eq28289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28289
  have eq28828 : (M.op x y) = (M.op x x) ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28807
  have eq28840 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq28330
       grind)
    | exact superpose eq28330 eq45
    | exact resolve eq45 eq28330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq28855 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq764 x y
       have i₂ := eq28330
       grind)
    | exact superpose eq28330 eq764
    | (have j0 := eq764 x y
       grind)
    | exact resolve eq764 eq28330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28330
  have eq28866 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28855
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28855
    | exact resolve eq28855 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28855
  have eq28878 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq28840
    | exact resolve eq28840 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28840
  have eq28883 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq28866
    | exact resolve eq28866 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28866
  have eq28891 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28883
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28883
    | exact resolve eq28883 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28883
  have eq28899 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28891
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28891
    | exact resolve eq28891 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28891
  have eq28909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28899
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28899
    | exact resolve eq28899 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28899
  have eq28920 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28909
    | exact resolve eq28909 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28909
  have eq28921 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq28920
  have eq28929 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28921
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28921
    | exact resolve eq28921 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28921
  have eq28936 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28929
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28929
    | exact resolve eq28929 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28929
  have eq30332 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28262 x X0
       have i₂ := eq28264
       grind)
    | exact superpose eq28264 eq28262
    | exact resolve eq28262 eq28264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28262
  have eq30416 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq30332 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30332
  have eq37216 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28264
       have i₂ := eq28828
       grind)
    | exact superpose eq28828 eq28264
    | exact resolve eq28264 eq28828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28264 eq28828
  have eq37247 : x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37216
  have eq37272 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37247 eq764
    | (have j0 := eq764 x (M.op x y)
       grind)
    | exact resolve eq764 eq37247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq37247
  have eq37278 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37272
  have eq37283 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37278
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37278
    | exact resolve eq37278 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37278
  have eq37300 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq37283
    | exact resolve eq37283 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37283
  have eq37308 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq37300
    | exact resolve eq37300 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37300
  have eq37316 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37308
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37308
    | exact resolve eq37308 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37308
  have eq40219 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq28936
  have eq40251 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq40219
    | exact resolve eq40219 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40219
  have eq41205 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37316 eq57
    | exact resolve eq57 eq37316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40251 eq28878
    | exact resolve eq28878 eq40251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28878 eq40251
  have eq41589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq41578
  have eq41598 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq41589
       have r₂ := eq28
       grind)
    | exact resolve eq41589 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41589
  have eq41611 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41598 eq57
    | exact resolve eq57 eq41598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41929 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41611 eq238
    | exact resolve eq238 eq41611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41611
  have eq47357 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41205 eq41929
    | exact resolve eq41929 eq41205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41205 eq41929
  have eq47384 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq47357
  have eq50824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq47384 eq37316
    | exact resolve eq37316 eq47384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37316 eq47384
  have eq50855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq50824
  have eq50871 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq50855
       have r₂ := eq28
       grind)
    | exact resolve eq50855 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50855
  have eq51181 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50871 eq57
    | exact resolve eq57 eq50871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50871
  have eq51219 : (M.op (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq51181
  have eq54050 : (τ (M.op (σ (M.op x y)) (σ x))) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51219 eq152
    | exact resolve eq152 eq51219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq51219
  have eq57348 : (τ (σ y)) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41598 eq54050
    | exact resolve eq54050 eq41598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41598 eq54050
  have eq57479 : (τ (σ y)) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq57348
  have eq57488 : y = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq57479
    | exact resolve eq57479 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57479
  have eq57501 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57488 eq28282
    | exact resolve eq28282 eq57488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28282 eq57488
  have eq57511 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq57501
  have eq57589 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57511 eq57
    | exact resolve eq57 eq57511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57511
  have eq57664 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30416 x
       have i₂ := eq57589
       grind)
    | exact superpose eq57589 eq30416
    | exact resolve eq30416 eq57589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30416 eq57589
  have eq57689 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq57664
  have eq58325 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57689 eq28297
    | exact resolve eq28297 eq57689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28297 eq57689
  have eq58350 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq58325
  have eq58366 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq58350
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58350
    | exact resolve eq58350 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58350
  have eq58367 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq58366
  have eq58656 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ y) X1)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq58367 eq55
    | exact resolve eq55 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58657 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58367 eq59
    | exact resolve eq59 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq58659 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) X1)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq58367 eq239
    | exact resolve eq239 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq58687 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq469 eq58659
    | (have j0 := eq58659 X0 (σ y)
       grind)
    | exact resolve eq58659 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58659
  have eq58692 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58657 eq189
    | exact resolve eq189 eq58657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq58695 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58657 eq238
    | exact resolve eq238 eq58657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq58734 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58657 eq6677
    | exact resolve eq6677 eq58657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6677
  have eq58750 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq58734
    | (have j0 := eq58734 X0
       grind)
    | exact resolve eq58734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58734
  have eq58757 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq469 eq58695
    | (have j0 := eq58695 (σ y)
       grind)
    | exact resolve eq58695 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq58695
  have eq58759 : x = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq58692
    | exact resolve eq58692 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58692
  have eq59073 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58757 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq58757
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq58757
       grind)
    | exact resolve eq12 eq58757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58757
  have eq59094 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq59073
  have eq59868 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq7191 eq58687
    | exact resolve eq58687 eq7191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7191
  have eq59871 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58657 eq58687
    | exact resolve eq58687 eq58657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58657 eq58687
  have eq59952 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq59871
  have eq60297 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq59952 eq57
    | exact resolve eq57 eq59952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59952
  have eq65550 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq59094 eq58656
    | exact resolve eq58656 eq59094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58656 eq59094
  have eq65578 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq65550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65550
  have eq71796 : (k y y) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq59868 eq124
    | exact resolve eq124 eq59868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59868
  have eq78347 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) X1)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq65578 eq56
    | exact resolve eq56 eq65578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq65578
  have eq81860 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq78347 eq58750
    | exact resolve eq58750 eq78347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58750 eq78347
  have eq81907 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq81860
  have eq81944 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58367 eq81907
    | exact resolve eq81907 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58367 eq81907
  have eq81969 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq81944
  have eq81982 : (τ (σ y)) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq81969 eq74
    | exact resolve eq74 eq81969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81969
  have eq82048 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq30 eq81982
    | exact resolve eq81982 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81982
  have eq82064 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq82048 eq74
    | exact resolve eq74 eq82048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82048
  have eq82126 : y = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq82064
    | exact resolve eq82064 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82064
  have eq82160 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq82126
       grind)
    | exact superpose eq82126 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq82126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82126
  have eq82190 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq82160
       have r₂ := eq82
       grind)
    | exact resolve eq82160 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82160
  have eq82216 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq82190
       have r₂ := eq12 x y
       grind)
    | exact resolve eq82190 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82190
  have eq84836 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq82216
       grind)
    | exact superpose eq82216 eq110
    | exact resolve eq110 eq82216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq82216
  have eq84870 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x y) := by grind
  clear eq84836
  have eq84879 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq84870
       have r₂ := eq82
       grind)
    | exact resolve eq84870 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84870
  have eq84883 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq84879
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq84879
    | exact resolve eq84879 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84879
  have eq99933 : (τ (σ y)) = (k x y) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq84883 eq74
    | exact resolve eq74 eq84883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq84883
  have eq100001 : y = (k x y) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq30 eq99933
    | exact resolve eq99933 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99933
  have eq105328 : x ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by grind
  clear eq100001
  have eq128889 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60297 eq71796
    | exact resolve eq71796 eq60297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60297 eq71796
  have eq129122 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq128889
  have eq129133 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq129122
    | exact resolve eq129122 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129122
  have eq129202 : (k (M.op (σ y) (σ y)) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq129133 eq464
    | exact resolve eq464 eq129133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq129248 : (σ y) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq129202
       have i₂ := eq57 sF3 sF3
       grind)
    | exact superpose eq57 eq129202
    | exact resolve eq129202 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129202
  have eq135918 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq129133 eq129248
    | exact resolve eq129248 eq129133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129133 eq129248
  have eq135941 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq135918
  have eq135954 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq135941 eq124
    | exact resolve eq124 eq135941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq135941
  have eq136062 : y = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq135954
    | exact resolve eq135954 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135954
  have eq136066 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq136062
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq136062
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq136062 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136097 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq136062
       grind)
    | exact superpose eq136062 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq136062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136106 : x ≠ y ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq136062
  have eq136115 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq136097
  have eq136131 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq136066
  have eq136531 : (k y y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq136115
  have eq136946 : (k y y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq136131
  have eq143351 : x ≠ (M.op y y) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq136531
  have eq144152 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq58759
       have i₂ := eq136946
       grind)
    | exact superpose eq136946 eq58759
    | exact resolve eq58759 eq136946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58759
  have eq144197 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq144152
  have eq144274 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57 y y
       have i₂ := eq144197
       grind)
    | exact superpose eq144197 eq57
    | exact resolve eq57 eq144197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144197
  have eq144318 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq144274
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq144274
    | exact resolve eq144274 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144274
  have eq144319 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq144318
  have eq144333 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144319 eq30
    | exact resolve eq30 eq144319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq144319
  have eq144858 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq144333
    | exact resolve eq144333 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq144333
  have eq144864 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq144858 eq21
    | exact resolve eq21 eq144858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144868 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq144858 eq58
    | exact resolve eq58 eq144858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq144870 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq144858 eq82
    | (have r₁ := eq82
       have r₂ := eq144858
       grind)
    | exact resolve eq82 eq144858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq144858
  have eq145046 : y = (M.op x x) ∨ x = (k x y) ∨ x = y := by grind
  clear eq144870
  have eq145185 : y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq145046
       have r₂ := eq105328
       grind)
    | exact resolve eq145046 eq105328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105328 eq145046
  have eq145189 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq144864
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq144864
    | exact resolve eq144864 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144864
  have eq147827 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq125
       have i₂ := eq144868
       grind)
    | exact superpose eq144868 eq125
    | exact resolve eq125 eq144868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq147830 : x ≠ x ∨ y = (M.op x y) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq143351
       have i₂ := eq144868
       grind)
    | exact superpose eq144868 eq143351
    | (have r₁ := eq143351
       have r₂ := eq144868
       grind)
    | exact resolve eq143351 eq144868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143351 eq144868
  have eq147887 : y = (M.op x y) ∨ x = (k y y) ∨ x = y := by grind
  clear eq147830
  have eq147889 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq147827
  have eq147908 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq147887
       have r₂ := eq136106
       grind)
    | exact resolve eq147887 eq136106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136106 eq147887
  have eq147909 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq147889
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq147889
    | exact resolve eq147889 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147889
  have eq153017 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq136946
       have i₂ := eq147908
       grind)
    | exact superpose eq147908 eq136946
    | exact resolve eq136946 eq147908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136946 eq147908
  have eq153049 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq153017
  have eq153416 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq145189 eq147909
    | exact resolve eq147909 eq145189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145189 eq147909
  have eq153489 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq153416
  have eq154912 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57 y y
       have i₂ := eq153049
       grind)
    | exact superpose eq153049 eq57
    | exact resolve eq57 eq153049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153049
  have eq154957 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq154912
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq154912
    | exact resolve eq154912 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154912
  have eq154958 : y = (M.op x y) := by grind
  clear eq154957
  have eq154967 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq154958 eq21
    | exact resolve eq21 eq154958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq155291 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq154967
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq154967
    | exact resolve eq154967 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154967
  have eq155633 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq155291 eq27
    | exact resolve eq27 eq155291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq161489 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq153489 eq7527
    | (have j0 := eq7527 (σ (M.op x y))
       grind)
    | exact resolve eq7527 eq153489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7527
  have eq161522 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq161489
  have eq161528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq155633 eq161522
    | exact resolve eq161522 eq155633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161522
  have eq161543 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq161528
       have r₂ := eq28
       grind)
    | exact resolve eq161528 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161528
  have eq161812 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq161543
  have eq165269 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq145185
  have eq165316 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq165269
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq165269
    | exact resolve eq165269 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq165269
  have eq165335 : y = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq154958 eq165316
    | exact resolve eq165316 eq154958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165316
  have eq171845 : x ≠ y ∨ x = (k x y) := by grind
  clear eq165335
  have eq178916 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq161812 eq153489
    | exact resolve eq153489 eq161812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153489 eq161812
  have eq178955 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq178916
  have eq179032 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq178955 eq57
    | exact resolve eq57 eq178955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq178955
  have eq179072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq155633 eq179032
    | exact resolve eq179032 eq155633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179032
  have eq179089 : x = y := by
    first
    | (have r₁ := eq179072
       have r₂ := eq28
       grind)
    | exact resolve eq179072 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179072
  have eq179101 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq179089
       grind)
    | exact superpose eq179089 eq25
    | exact resolve eq25 eq179089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq179364 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq171845
       have i₂ := eq179089
       grind)
    | exact superpose eq179089 eq171845
    | (have r₁ := eq171845
       have r₂ := eq179089
       grind)
    | exact resolve eq171845 eq179089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171845
  have eq179368 : x = (k x x) := by grind
  clear eq179364
  have eq179647 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq155291 eq179101
    | exact resolve eq179101 eq155291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155291 eq179101
  have eq179860 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq179647
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq179647
    | exact resolve eq179647 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179647
  have eq181607 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq179860 eq155633
    | exact resolve eq155633 eq179860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155633
  have eq184259 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq181607 eq213
    | exact resolve eq213 eq181607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq181607
  have eq184344 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq184259
       have r₂ := eq28
       grind)
    | exact resolve eq184259 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184259
  have eq184362 : (k y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq154958 eq184344
    | exact resolve eq184344 eq154958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154958 eq184344
  have eq184375 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq184362
       have i₂ := eq179089
       grind)
    | exact superpose eq179089 eq184362
    | exact resolve eq184362 eq179089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179089 eq184362
  have eq184388 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq184375
       have i₂ := eq179368
       grind)
    | exact superpose eq179368 eq184375
    | exact resolve eq184375 eq179368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179368 eq184375
  have eq184423 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq184388 eq15
    | exact resolve eq15 eq184388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184388
  have eq184923 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184423
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq184423
    | exact resolve eq184423 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq184423
  have eq185105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq179860 eq184923
    | exact resolve eq184923 eq179860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179860 eq184923
  have eq185222 : False := by grind
  exact eq185222

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pxy_y_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  clear eq22
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
  have eq78 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq204 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq27
    | exact resolve eq27 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq79
    | (have r₁ := eq79
       have r₂ := eq202
       grind)
    | exact resolve eq79 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq202
  have eq438 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq437
  have eq441 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq438 eq129
    | exact resolve eq129 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq445 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq441
  have eq450 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq445
       have r₂ := eq204
       grind)
    | exact resolve eq445 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq445
  have eq455 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq450 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq458 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq86 (σ x) (σ y)
       grind)
    | (have r₁ := eq455
       have r₂ := eq86 (σ x) (σ y)
       grind)
    | exact resolve eq455 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq461 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq458
    | exact resolve eq458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq461 eq129
    | exact resolve eq129 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq461
  have eq518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq515
  have eq522 : y = (M.op x y) := by
    first
    | (have r₁ := eq518
       have r₂ := eq27
       grind)
    | exact resolve eq518 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq524 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq522 eq20
    | exact resolve eq20 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq528 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq522 eq78
    | (have r₁ := eq78
       have r₂ := eq522
       grind)
    | exact resolve eq78 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq534 : y = (k x y) ∨ y = (M.op y x) := by grind
  clear eq528
  have eq540 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq524
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq524
    | exact resolve eq524 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq543 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq540 eq26
    | exact resolve eq26 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1075 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq534
       grind)
    | exact superpose eq534 eq44
    | exact resolve eq44 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq1082 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq540 eq1075
    | exact resolve eq1075 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1084 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1082
    | exact resolve eq1082 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1085 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq540 eq1084
    | exact resolve eq1084 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1088 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1085 eq86
    | (have j0 := eq86 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq86 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1089 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq1088
  have eq1091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq543 eq1089
    | exact resolve eq1089 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1094 : y = (M.op y x) := by
    first
    | (have r₁ := eq1091
       have r₂ := eq27
       grind)
    | exact resolve eq1091 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1104 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1094
       grind)
    | exact superpose eq1094 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1122 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq86 x y
       grind)
    | (have r₁ := eq1104
       have r₂ := eq86 x y
       grind)
    | exact resolve eq1104 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1130 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1122
    | exact resolve eq1122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1122
  have eq1133 : y = (k x y) := by
    first
    | exact superpose eq522 eq1130
    | exact resolve eq1130 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq1130
  have eq1146 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1133
       grind)
    | exact superpose eq1133 eq44
    | exact resolve eq44 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1133
  have eq1153 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq540 eq1146
    | exact resolve eq1146 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1155 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1153
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1153
    | exact resolve eq1153 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1153
  have eq1156 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq540 eq1155
    | exact resolve eq1155 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq1155
  have eq1221 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1156 eq86
    | (have j0 := eq86 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq86 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1156
  have eq1222 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1221
  have eq1224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq543 eq1222
    | exact resolve eq1222 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq1222
  have eq1227 : False := by grind
  exact eq1227

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_x_pxy_x_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq58 X0 (τ X1)
       grind)
    | exact superpose eq58 eq18
    | (have j1 := eq58 X0 (τ X1)
       grind)
    | exact resolve eq18 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq84 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
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
  clear eq18
  have eq85 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq85
    | exact resolve eq85 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq85
  have eq104 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq10
    | exact resolve eq10 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq119 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 x y
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 x y
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq365 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) ≠ X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (τ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (M.op (τ X1) (τ X1)) (τ X1)
       have r₂ := eq75 (M.op (τ X1) (τ X1)) X1
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 X0 (τ X1)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq387 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq374 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq390 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (τ (M.op X1 X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 X1
       have i₂ := eq104 X1
       grind)
    | exact superpose eq104 eq387
    | (have j0 := eq387 X0 X1
       grind)
    | exact resolve eq387 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq391 : ∀ X0 X1 : G, (τ (M.op X1 X1)) ≠ X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq104 X1
       grind)
    | exact superpose eq104 eq373
    | (have j0 := eq373 X0 X1
       grind)
    | (have r₁ := eq373 (τ (M.op X0 X0)) X0
       have r₂ := eq104 X0
       grind)
    | exact resolve eq373 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq373
  have eq397 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq365
    | (have j0 := eq365 X0 X1
       grind)
    | exact resolve eq365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq6541 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       have j1 := eq390 X0 X1
       grind)
    | (have r₁ := eq391 (k (τ (M.op X1 X1)) (τ X1)) X1
       have r₂ := eq390 (τ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq391 X0 X1
       have r₂ := eq390 X0 X1
       grind)
    | (have r₁ := eq391 (τ (M.op X1 X1)) X1
       have r₂ := eq390 (τ (M.op X1 X1)) X1
       grind)
    | exact resolve eq391 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq391
  have eq6542 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6541 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6541
    | exact resolve eq6541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6541
  have eq6629 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6542 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6542
    | (have j0 := eq6542 X0 X1
       grind)
    | exact resolve eq6542 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6542
  have eq6713 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq6629 y x
       grind)
    | exact superpose eq6629 eq119
    | (have j1 := eq6629 y x
       grind)
    | (have r₁ := eq119
       have r₂ := eq6629 y x
       grind)
    | exact resolve eq119 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq6714 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq6629 X1 X0
       grind)
    | exact superpose eq6629 eq10
    | (have j1 := eq6629 X1 X0
       grind)
    | exact resolve eq10 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6629
  have eq6775 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6713
  have eq6790 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6714 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq6714
    | (have j0 := eq6714 X0 X1
       grind)
    | exact resolve eq6714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714
  have eq6933 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6790 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6790
  have eq7043 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127 x y
       have i₂ := eq6775
       grind)
    | exact superpose eq6775 eq127
    | (have j0 := eq127 x y
       grind)
    | exact resolve eq127 eq6775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq6775
  have eq7056 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7043
  have eq7057 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7056
  have eq7063 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7057
       grind)
    | exact superpose eq7057 eq16
    | exact resolve eq16 eq7057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7099 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6933 (σ x) (σ y)
       have i₂ := eq7057
       grind)
    | exact superpose eq7057 eq6933
    | (have j0 := eq6933 (σ x) (σ y)
       grind)
    | (have r₁ := eq6933 (σ x) (σ y)
       have r₂ := eq7057
       grind)
    | exact resolve eq6933 eq7057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6933 eq7057
  have eq7100 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq7099
  have eq7102 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq7100
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7100
    | exact resolve eq7100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7100
  have eq7204 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq397 y x
       have i₂ := eq7102
       grind)
    | exact superpose eq7102 eq397
    | (have j0 := eq397 y x
       grind)
    | exact resolve eq397 eq7102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq7102
  have eq7282 : x = (M.op x y) := by
    first
    | (have r₁ := eq7204
       have r₂ := eq7063
       grind)
    | exact resolve eq7204 eq7063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7204
  have eq7449 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq7063
       have i₂ := eq7282
       grind)
    | exact superpose eq7282 eq7063
    | exact resolve eq7063 eq7282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063 eq7282
  have eq7488 : False := by grind
  exact eq7488

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq124 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq133 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq124
    | (have j0 := eq124 X0
       grind)
    | exact resolve eq124 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq124
  have eq135 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq133
    | (have j0 := eq133 X0
       grind)
    | exact resolve eq133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq136 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq135 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq135 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq135 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq143 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq136 (σ X0)
       grind)
    | exact superpose eq136 eq15
    | exact resolve eq15 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq143 X0
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq143
    | exact resolve eq143 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq143
  have eq313 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq820 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq320 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq320
    | (have j0 := eq320 (τ X0) (τ X1)
       grind)
    | exact resolve eq320 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq827 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq820 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq820
    | (have j0 := eq820 X0 X1
       grind)
    | exact resolve eq820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq830 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq827
    | (have j0 := eq827 X0 X1
       grind)
    | exact resolve eq827 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq832 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq830
    | (have j0 := eq830 X0 X1
       grind)
    | exact resolve eq830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq833 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq832 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq832
    | (have j0 := eq832 X0 X1
       grind)
    | exact resolve eq832 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq834 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq833 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq833
    | (have j0 := eq833 X0 X1
       grind)
    | exact resolve eq833 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq835 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq834 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq834
    | (have j0 := eq834 X0 X1
       grind)
    | exact resolve eq834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq313
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq313
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq313
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq313
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq313 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq996 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq995
  have eq7585 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq16
    | exact resolve eq16 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq7586 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7585
       have r₂ := eq150 x
       grind)
    | exact resolve eq7585 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7585
  have eq7589 : y ≠ y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq7586
       grind)
    | exact superpose eq7586 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq7586
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7586
       grind)
    | exact resolve eq12 eq7586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7586
  have eq7607 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7589
  have eq7616 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq320 x y
       have i₂ := eq7607
       grind)
    | exact superpose eq7607 eq320
    | (have j0 := eq320 x y
       grind)
    | exact resolve eq320 eq7607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq7607
  have eq7623 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7616
  have eq7624 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7623
  have eq7741 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7624
       grind)
    | exact superpose eq7624 eq16
    | exact resolve eq16 eq7624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7750 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq7624
       grind)
    | exact superpose eq7624 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7624
       grind)
    | exact resolve eq12 eq7624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7624
  have eq7769 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq7750
  have eq7785 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq7769
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7769
    | exact resolve eq7769 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7769
  have eq7907 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7785
       grind)
    | exact superpose eq7785 eq10
    | exact resolve eq10 eq7785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7785
  have eq7977 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq7907
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7907
    | exact resolve eq7907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7907
  have eq7986 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7977
       grind)
    | exact superpose eq7977 eq16
    | exact resolve eq16 eq7977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7977
  have eq7987 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq7986
       have r₂ := eq150 x
       grind)
    | exact resolve eq7986 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7986
  have eq8253 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq7987
       grind)
    | exact superpose eq7987 eq10
    | exact resolve eq10 eq7987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7987
  have eq8328 : y = (k x y) := by
    first
    | (have i₁ := eq8253
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8253
    | exact resolve eq8253 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8253
  have eq8353 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq835 x y
       have i₂ := eq8328
       grind)
    | exact superpose eq8328 eq835
    | (have j0 := eq835 x y
       grind)
    | (have r₁ := eq835 x y
       have r₂ := eq8328
       grind)
    | exact resolve eq835 eq8328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq8328
  have eq8357 : x = y ∨ y = (M.op x y) := by grind
  clear eq8353
  have eq8598 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8357
       grind)
    | exact superpose eq8357 eq16
    | exact resolve eq16 eq8357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8357
  have eq8603 : y = (M.op x y) := by
    first
    | (have r₁ := eq8598
       have r₂ := eq150 x
       grind)
    | exact resolve eq8598 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8598
  have eq8607 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7741
       have i₂ := eq8603
       grind)
    | exact superpose eq8603 eq7741
    | exact resolve eq7741 eq8603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7741 eq8603
  have eq8631 : (σ x) = (σ y) := by grind
  clear eq8607
  have eq8786 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8631
       grind)
    | exact superpose eq8631 eq10
    | exact resolve eq10 eq8631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8631
  have eq8866 : x = y := by
    first
    | (have i₁ := eq8786
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8786
    | exact resolve eq8786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8786
  have eq8886 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8866
       grind)
    | exact superpose eq8866 eq16
    | exact resolve eq16 eq8866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8866
  have eq8892 : False := by grind
  exact eq8892

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq32 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq40 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq52 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq47
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq161 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq165 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq161 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq161 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq161 X1 X1
       have r₂ := eq55 X1 X1
       grind)
    | exact resolve eq161 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq161
  have eq466 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq165 (σ X0) (σ X1)
       grind)
    | exact superpose eq165 eq15
    | exact resolve eq15 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq165 X0 X1
       grind)
    | exact superpose eq165 eq466
    | exact resolve eq466 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq466
  have eq473 : False := by grind
  exact eq473

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
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
  clear eq36
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq44
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq44 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq107
    | exact resolve eq107 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110 eq75
    | (have j0 := eq75 (σ x) (σ y)
       grind)
    | exact resolve eq75 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq123
       have r₂ := eq27
       grind)
    | exact resolve eq123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq223 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq128 eq51
    | exact resolve eq51 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq223 eq14
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq223 eq53
    | exact resolve eq53 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq415 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq53 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq53 X0 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq232 X0 x
       have i₂ := eq405 X0 x
       grind)
    | exact superpose eq405 eq232
    | exact resolve eq232 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq501 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq518 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq501
    | (have j0 := eq501 (σ y)
       grind)
    | exact resolve eq501 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq569 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq518
    | exact resolve eq518 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq518
  have eq580 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq569
  have eq596 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq580 eq405
    | exact resolve eq405 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq580
  have eq603 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq596
  have eq622 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq603 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq603
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq603
       grind)
    | exact resolve eq13 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq624 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq622
  have eq630 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq624
    | exact resolve eq624 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq630 eq110
    | exact resolve eq110 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq630
  have eq676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq673
  have eq678 : x = (M.op x y) := by
    first
    | (have r₁ := eq676
       have r₂ := eq27
       grind)
    | exact resolve eq676 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq680 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq678 eq20
    | exact resolve eq20 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq682 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x x)) := by
    intro X0
    first
    | exact superpose eq678 eq50
    | exact resolve eq50 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq683 : x ≠ x ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq678 eq63
    | (have r₁ := eq63
       have r₂ := eq678
       grind)
    | exact resolve eq63 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq690 : (k y x) = (M.op y x) := by grind
  clear eq683
  have eq696 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq680
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq680
    | exact resolve eq680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq680
  have eq762 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq696 eq26
    | exact resolve eq26 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq767 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq696 eq51
    | exact resolve eq51 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq809 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq72
    | exact resolve eq72 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq690
  have eq810 : (k (σ y) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq696 eq809
    | exact resolve eq809 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq1001 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) X0 (M.op x x)
       have i₂ := eq682 (M.op x x)
       grind)
    | exact superpose eq682 eq14
    | exact resolve eq14 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op x x) X1
       have i₂ := eq682 x
       grind)
    | exact superpose eq682 eq14
    | exact resolve eq14 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1009 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op x x) X1
       have i₂ := eq682 x
       grind)
    | exact superpose eq682 eq53
    | exact resolve eq53 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq1154 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq767 eq1004
    | exact resolve eq1004 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq1162 : ∀ X0 X2 : G, (M.op X0 x) = (M.op (M.op X2 X2) x) := by
    intro X0 X2
    first
    | (have i₁ := eq53 x X2 (M.op (M.op X0 x) X0)
       have i₂ := eq1004 X0 x
       grind)
    | exact superpose eq1004 eq53
    | exact resolve eq53 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1165 : ∀ X0 : G, (M.op x x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1162 X0 x
       have i₂ := eq1001 x
       grind)
    | exact superpose eq1001 eq1162
    | exact resolve eq1162 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq1162
  have eq1249 : (k (σ y) (σ (M.op x y))) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq810
       have i₂ := eq1165 y
       grind)
    | exact superpose eq1165 eq810
    | exact resolve eq810 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq1165
  have eq1545 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1004 X0 x
       have i₂ := eq1009 X0 x
       grind)
    | exact superpose eq1009 eq1004
    | exact resolve eq1004 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1585 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1545 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1545
    | (have j0 := eq1545 y
       grind)
    | exact resolve eq1545 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1545
  have eq1600 : y = (M.op x x) := by
    first
    | exact superpose eq678 eq1585
    | exact resolve eq1585 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq1585
  have eq1604 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1249
       have i₂ := eq1600
       grind)
    | exact superpose eq1600 eq1249
    | exact resolve eq1249 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249 eq1600
  have eq1651 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1604
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1604
    | exact resolve eq1604 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1604
  have eq1734 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op X0 X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq696 eq224
    | exact resolve eq224 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq696
  have eq1735 : ∀ X0 : G, (M.op (M.op X0 X0) (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1154 eq1734
    | exact resolve eq1734 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154 eq1734
  have eq1802 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1651 eq75
    | (have j0 := eq75 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq75 eq1651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1803 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq1802
  have eq1872 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1803 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq1803
       grind)
    | exact resolve eq12 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1881 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1872
  have eq1883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq762 eq1881
    | exact resolve eq1881 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881
  have eq1884 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1883
       have r₂ := eq27
       grind)
    | exact resolve eq1883 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1885 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1651 eq1884
    | exact resolve eq1884 eq1651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651 eq1884
  have eq1974 : (M.op (σ y) (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq1885 eq1009
    | exact resolve eq1009 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1975 : (σ y) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq1803 eq1974
    | exact resolve eq1974 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803 eq1974
  have eq2372 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 X0) (M.op x (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1735 eq415
    | exact resolve eq415 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq1735
  have eq2426 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1975 eq2372
    | exact resolve eq2372 eq1975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975 eq2372
  have eq2450 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1885 eq2426
    | exact resolve eq2426 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq2535 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2450 eq2426
    | exact resolve eq2426 eq2450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426 eq2450
  have eq2548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq762 eq2535
    | exact resolve eq2535 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq2535
  have eq2561 : False := by grind
  exact eq2561

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq43 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq15
    | exact resolve eq15 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq57
    | exact resolve eq57 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq57
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X0) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq80
    | (have j0 := eq80 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq80 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq157
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq157
    | (have j1 := eq80 (σ x) (σ y)
       grind)
    | (have r₁ := eq157
       have r₂ := eq80 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq157
       have r₂ := eq80 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq157 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq157
  have eq274 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq271
  have eq275 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq274
       grind)
    | exact superpose eq274 eq16
    | exact resolve eq16 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq276 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq275
       have r₂ := eq66 x
       grind)
    | exact resolve eq275 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq312 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq276
       grind)
    | exact superpose eq276 eq10
    | exact resolve eq10 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq329 : x = y := by
    first
    | (have i₁ := eq312
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq312
    | exact resolve eq312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq373 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq329
       grind)
    | exact superpose eq329 eq16
    | exact resolve eq16 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq374 : False := by grind
  exact eq374

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_y_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X0
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq16 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq395 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq311 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq311
    | exact resolve eq311 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq554 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X1 X3 x
       have i₂ := eq178 X1 X0 x
       grind)
    | (have i₁ := eq178 X0 X1 X0
       have i₂ := eq178 X0 X0 x
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 x
       have i₂ := eq178 X1 X0 x
       grind)
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq178 X0 X0 X2
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq178
    | exact resolve eq178 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (k X0 X1) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1011 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (k (M.op X0 X1) X0)) = X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 (M.op X0 X1) X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op X0 X1) X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1032 : (M.op x y) = (k x y) ∨ x = (M.op x x) := by
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
  have eq1035 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1040 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1032
       grind)
    | exact superpose eq1032 eq41
    | exact resolve eq41 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1076 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1075
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1075
    | exact resolve eq1075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1078 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1076
    | exact resolve eq1076 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1078 eq1035
    | exact resolve eq1035 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq1078
  have eq1095 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1088
       have r₂ := eq27
       grind)
    | exact resolve eq1088 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1108 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1095 eq179
    | exact resolve eq179 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1129 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1095 eq1108
    | exact resolve eq1108 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095 eq1108
  have eq1156 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1129 eq142
    | exact resolve eq142 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1129
  have eq1159 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq1156
    | exact resolve eq1156 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1156
  have eq1162 : x = (M.op x x) := by
    first
    | (have j1 := eq1040 x
       grind)
    | (have r₁ := eq1159
       have r₂ := eq1040 x
       grind)
    | exact resolve eq1159 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1170 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x X1
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq16
    | exact resolve eq16 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 x X1
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq178
    | exact resolve eq178 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq179
    | exact resolve eq179 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1 x
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq554
    | exact resolve eq554 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq1182 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq600 X0 x
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq600
    | exact resolve eq600 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1194 : x = (k x x) := by
    first
    | (have i₁ := eq1174
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq1174
    | exact resolve eq1174 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq1174
  have eq1196 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1170 X0 x
       have i₂ := eq1173 X0 x
       grind)
    | exact superpose eq1173 eq1170
    | exact resolve eq1170 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1221 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1194
       grind)
    | exact superpose eq1194 eq40
    | exact resolve eq40 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1194
  have eq1224 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1221
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1221
    | exact resolve eq1221 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1221
  have eq1229 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1224 eq1040
    | (have j0 := eq1040 (σ x)
       grind)
    | (have r₁ := eq1040 (σ x)
       have r₂ := eq1224
       grind)
    | exact resolve eq1040 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq1224
  have eq1230 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1229
  have eq1242 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | exact superpose eq1230 eq178
    | exact resolve eq178 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1249 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1230 eq562
    | exact resolve eq562 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1251 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq1230 eq600
    | exact resolve eq600 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq1230
  have eq1262 : ∀ X1 : G, (M.op (σ x) (M.op x X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq1249 x X1
       have i₂ := eq1178 x X1
       grind)
    | exact superpose eq1178 eq1249
    | exact resolve eq1249 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1367 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1196 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1196
    | (have j0 := eq1196 y
       grind)
    | exact resolve eq1196 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1508 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq1262 (M.op x X0)
       have i₂ := eq1196 X0
       grind)
    | exact superpose eq1196 eq1262
    | exact resolve eq1262 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1510 : y = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq1262 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1262
    | (have j0 := eq1262 y
       grind)
    | exact resolve eq1262 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1511 : (M.op x y) = (M.op (σ x) y) := by
    first
    | exact superpose eq1367 eq1262
    | exact resolve eq1262 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq1367
  have eq1954 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1173 (M.op X0 X1) X0
       have i₂ := eq1173 X0 X1
       grind)
    | exact superpose eq1173 eq1173
    | exact resolve eq1173 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq2074 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (σ x) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1954 X0 X1
       have i₂ := eq1508 X0
       grind)
    | exact superpose eq1508 eq1954
    | exact resolve eq1954 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq2103 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op X0 X1)) = (M.op (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2074 X0 X1
       have i₂ := eq1508 (M.op X0 X1)
       grind)
    | exact superpose eq1508 eq2074
    | exact resolve eq2074 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074
  have eq2505 : (σ (M.op x y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq1182 y
       grind)
    | exact superpose eq1182 eq41
    | exact resolve eq41 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2509 : (k (τ (M.op (σ y) (σ y))) y) = (τ (M.op x (σ y))) := by
    first
    | (have i₁ := eq153 (M.op sF3 sF3)
       have i₂ := eq1182 sF3
       grind)
    | exact superpose eq1182 eq153
    | exact resolve eq153 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1182
  have eq2510 : (k (τ (M.op (σ y) (σ y))) y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2509
       have i₂ := eq1508 sF3
       grind)
    | exact superpose eq1508 eq2509
    | exact resolve eq2509 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2509
  have eq2514 : (σ (M.op x y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq2505
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2505
    | exact resolve eq2505 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2505
  have eq2530 : (k (τ (M.op (σ y) (σ y))) y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2510
    | exact resolve eq2510 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq2533 : (σ (M.op x y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | exact superpose eq20 eq2514
    | exact resolve eq2514 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514
  have eq2560 : (σ (M.op x y)) = (k (σ (k y y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2533
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq2533
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq2533 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2567 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2560
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq2560
    | exact resolve eq2560 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq2571 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2567
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2567
    | exact resolve eq2567 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567
  have eq2574 : (τ (M.op (σ x) (σ y))) = (k (τ (k (σ y) (σ y))) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2530
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq2530
    | (have j1 := eq28 (σ y) x
       grind)
    | exact resolve eq2530 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2579 : (τ (M.op (σ x) (σ y))) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq116 eq2574
    | exact resolve eq2574 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq2574
  have eq3403 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (k (k X0 X1) X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1007 X0 X1 X2
       have i₂ := eq28 (k X0 X1) X0
       grind)
    | exact superpose eq28 eq1007
    | (have j0 := eq1007 X0 X1 X2
       have j1 := eq28 X0 X1
       grind)
    | exact resolve eq1007 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq3471 : ∀ X0 X1 : G, (M.op x (k (k X0 X1) X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3403 X0 X1 x
       have i₂ := eq1178 x (k (k X0 X1) X0)
       grind)
    | exact superpose eq1178 eq3403
    | (have j0 := eq3403 X0 X1 x
       grind)
    | exact resolve eq3403 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq3507 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) (k (k X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3471 X0 X1
       have i₂ := eq1508 (k (k X0 X1) X0)
       grind)
    | exact superpose eq1508 eq3471
    | (have j0 := eq3471 X0 X1
       grind)
    | exact resolve eq3471 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471
  have eq10988 : ∀ X0 : G, (M.op (σ x) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq1511 eq2103
    | exact resolve eq2103 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq12425 : ∀ X0 : G, (M.op (σ x) (k y X0)) = (M.op (M.op x y) (k y X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq10988 x
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq10988
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq10988 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq10988
  have eq13207 : (k (σ (k y y)) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq2579
       grind)
    | exact superpose eq2579 eq41
    | exact resolve eq41 eq2579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq13212 : (M.op (σ x) (σ y)) = (k (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13207
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq13207
    | exact resolve eq13207 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13207
  have eq13215 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13212
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq13212
    | exact resolve eq13212 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq13212
  have eq13216 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13215
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13215
    | exact resolve eq13215 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq13223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq13216 eq2571
    | exact resolve eq2571 eq13216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq13228 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq13223
       have r₂ := eq27
       grind)
    | exact resolve eq13223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13223
  have eq13236 : (k (τ (σ y)) y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq13228 eq2530
    | exact resolve eq2530 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13290 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq13228 eq1242
    | exact resolve eq1242 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13298 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq13290
    | exact resolve eq13290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13290
  have eq13328 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq13236
    | exact resolve eq13236 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13236
  have eq13330 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13228 eq13298
    | exact resolve eq13298 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13298
  have eq13349 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2533
       have i₂ := eq13330
       grind)
    | exact superpose eq13330 eq2533
    | exact resolve eq2533 eq13330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13395 : (M.op y y) = (M.op (σ x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1242 y y
       have i₂ := eq13330
       grind)
    | exact superpose eq13330 eq1242
    | exact resolve eq1242 eq13330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13330
  have eq13403 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1511 eq13395
    | exact resolve eq13395 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13395
  have eq13431 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13349
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13349
    | exact resolve eq13349 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13349
  have eq13682 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2533
       have i₂ := eq13403
       grind)
    | exact superpose eq13403 eq2533
    | exact resolve eq2533 eq13403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533 eq13403
  have eq13756 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13682
    | exact resolve eq13682 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13682
  have eq13820 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13431 eq13216
    | exact resolve eq13216 eq13431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13216 eq13431
  have eq13847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13756 eq13820
    | exact resolve eq13820 eq13756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13756 eq13820
  have eq13854 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13847
       have r₂ := eq27
       grind)
    | exact resolve eq13847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13847
  have eq14003 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13854 eq1242
    | exact resolve eq1242 eq13854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14011 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14003
    | exact resolve eq14003 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14003
  have eq14046 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13854 eq14011
    | exact resolve eq14011 eq13854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13854 eq14011
  have eq14047 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14046
  have eq14072 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq14047 eq27
    | exact resolve eq27 eq14047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq14385 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) ∨ (τ (M.op (σ y) (σ y))) = (M.op (σ x) (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq2530 eq3507
    | (have j0 := eq3507 (τ (M.op (σ x) (σ y))) x
       grind)
    | exact resolve eq3507 eq2530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530 eq3507
  have eq14556 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) ∨ (τ (M.op (σ y) (σ y))) = (M.op (σ x) (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq14047 eq14385
    | exact resolve eq14385 eq14047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14385
  have eq14573 : y = (M.op y y) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) ∨ (τ (M.op (σ y) (σ y))) = (M.op (σ x) (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq32 eq14556
    | exact resolve eq14556 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14556
  have eq14575 : (τ (M.op (σ y) (σ y))) = (M.op (σ x) (τ (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))))) ∨ y = (M.op y y) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq14573
       have i₂ := eq395 (M.op sF3 sF3) sF4
       grind)
    | exact superpose eq395 eq14573
    | exact resolve eq14573 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq14573
  have eq14576 : (τ (M.op (σ y) (σ y))) = (M.op (σ x) (τ (k (σ y) (M.op (σ y) (σ y))))) ∨ y = (M.op y y) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq14047 eq14575
    | exact resolve eq14575 eq14047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14575
  have eq14577 : (τ (M.op (σ y) (σ y))) = (M.op (σ x) (k y (τ (M.op (σ y) (σ y))))) ∨ y = (M.op y y) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq108 eq14576
    | exact resolve eq14576 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq14576
  have eq14578 : (τ (M.op (σ y) (σ y))) = (M.op (M.op x y) (k y (τ (M.op (σ y) (σ y))))) ∨ y = (M.op y y) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq12425 eq14577
    | exact resolve eq14577 eq12425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12425 eq14577
  have eq14579 : (τ (σ y)) = (M.op (M.op x y) (k y (τ (σ y)))) ∨ y = (M.op y y) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq13228 eq14578
    | exact resolve eq14578 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14578
  have eq14580 : y = (M.op (M.op x y) (k y y)) ∨ y = (M.op y y) ∨ (τ (M.op (σ y) (σ y))) = (M.op (τ (M.op (σ y) (σ y))) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq14579
    | exact resolve eq14579 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14579
  have eq14581 : y = (M.op (M.op x y) (k y y)) ∨ y = (M.op y y) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq13228 eq14580
    | exact resolve eq14580 eq13228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13228 eq14580
  have eq14582 : y = (M.op y y) ∨ y = (M.op (M.op x y) (k y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq14581
    | exact resolve eq14581 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14581
  have eq14583 : y = (M.op y y) ∨ y = (M.op (M.op x y) (k y y)) := by grind
  clear eq14582
  have eq14584 : y = (M.op y y) ∨ y = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq13328 eq14583
    | exact resolve eq14583 eq13328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14583
  have eq14585 : y = (M.op (M.op x y) (τ (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq14047 eq14584
    | exact resolve eq14584 eq14047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14584
  have eq14586 : y = (M.op (M.op x y) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq14585
    | exact resolve eq14585 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14585
  have eq15207 : (M.op (σ x) (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq14586 eq1242
    | exact resolve eq1242 eq14586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242 eq14586
  have eq15215 : y = (M.op y (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1510 eq15207
    | exact resolve eq15207 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510 eq15207
  have eq15397 : ∀ X0 : G, y = (M.op (M.op X0 X0) (k y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq15215 eq1011
    | exact resolve eq1011 eq15215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011 eq15215
  have eq15404 : ∀ X0 : G, y = (M.op (M.op X0 X0) (k y y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq15397 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15397
  have eq15408 : y = (M.op x (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15404 x
       have i₂ := eq1178 x (k y y)
       grind)
    | exact superpose eq1178 eq15404
    | exact resolve eq15404 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq15404
  have eq15409 : y = (M.op (σ x) (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15408
       have i₂ := eq1508 (k y y)
       grind)
    | exact superpose eq1508 eq15408
    | exact resolve eq15408 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508 eq15408
  have eq15410 : y = (M.op (σ x) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq13328 eq15409
    | exact resolve eq15409 eq13328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13328 eq15409
  have eq15411 : y = (M.op (σ x) (τ (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq14047 eq15410
    | exact resolve eq15410 eq14047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14047 eq15410
  have eq15412 : y = (M.op (σ x) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq15411
    | exact resolve eq15411 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq15411
  have eq15413 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1511 eq15412
    | exact resolve eq15412 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15412
  have eq15428 : (k y y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq15413
       grind)
    | exact superpose eq15413 eq179
    | exact resolve eq179 eq15413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq15447 : (k y y) = (M.op (σ x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1251 y
       have i₂ := eq15413
       grind)
    | exact superpose eq15413 eq1251
    | exact resolve eq1251 eq15413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq15483 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1511 eq15447
    | exact resolve eq15447 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511 eq15447
  have eq15500 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15413 eq15428
    | exact resolve eq15428 eq15413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15413 eq15428
  have eq15520 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15483 eq15500
    | exact resolve eq15500 eq15483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15483 eq15500
  have eq15521 : y = (M.op x y) := by grind
  clear eq15520
  have eq15532 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15521
       grind)
    | exact superpose eq15521 eq24
    | exact resolve eq24 eq15521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15521
  have eq15575 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15532 eq20
    | exact resolve eq20 eq15532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15532
  have eq15599 : False := by grind
  exact eq15599
