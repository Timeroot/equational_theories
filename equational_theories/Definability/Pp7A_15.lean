import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_x_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq77 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq80 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq57
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq80
  have eq83 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq76
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
  clear eq90
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq101
    | exact resolve eq101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq243 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq28 eq53
    | (have j0 := eq53 (σ y) (σ x)
       grind)
    | exact resolve eq53 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq926 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq51
    | (have j1 := eq73 X0 X0
       grind)
    | exact resolve eq51 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq948 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq3536 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X0 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq824
    | exact resolve eq824 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq3574 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq28 eq3536
    | (have j0 := eq3536 (σ y) (σ x)
       grind)
    | exact resolve eq3536 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536
  have eq4265 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq948 (τ X0)
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq948
    | (have j0 := eq948 (τ X0)
       grind)
    | exact resolve eq948 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq4286 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4265 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4265
    | (have j0 := eq4265 X0
       grind)
    | exact resolve eq4265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4265
  have eq4299 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4286 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4286
    | (have j0 := eq4286 X0
       grind)
    | exact resolve eq4286 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4286
  have eq4625 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq828 X0 X0 X2 X3 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq828
    | exact resolve eq828 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq21414 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4625 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq51 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq4625
    | exact resolve eq4625 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq4625
  have eq30316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq30317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq30316
    | exact resolve eq30316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30316
  have eq30328 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq30317
       have r₂ := eq29
       grind)
    | exact resolve eq30317 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30317
  have eq30360 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30328 eq53
    | exact resolve eq53 eq30328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30328
  have eq30382 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq30360
  have eq30455 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30382 eq21414
    | exact resolve eq21414 eq30382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30382
  have eq30459 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq30455
    | exact resolve eq30455 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30455
  have eq30511 : x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq30459
       grind)
    | exact superpose eq30459 eq53
    | exact resolve eq53 eq30459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30459
  have eq30533 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30511
  have eq30572 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq30588 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq30533
       grind)
    | exact superpose eq30533 eq53
    | exact resolve eq53 eq30533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq30607 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21414 y y
       have i₂ := eq30533
       grind)
    | exact superpose eq30533 eq21414
    | exact resolve eq21414 eq30533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21414 eq30533
  have eq30611 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30607
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq30607
    | exact resolve eq30607 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30607
  have eq30634 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30611 eq29
    | exact resolve eq29 eq30611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30637 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30611 eq243
    | exact resolve eq243 eq30611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq30645 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30611 eq3574
    | exact resolve eq3574 eq30611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3574
  have eq30701 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq30645
    | exact resolve eq30645 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30645
  have eq31423 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq30588
       grind)
    | exact superpose eq30588 eq83
    | exact resolve eq83 eq30588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq30588
  have eq31480 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31423
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq31423
    | exact resolve eq31423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31423
  have eq34830 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30701 eq30637
    | exact resolve eq30637 eq30701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30637 eq30701
  have eq34878 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq34830
  have eq34894 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30611 eq34878
    | exact resolve eq34878 eq30611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30611 eq34878
  have eq34930 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq34894
  have eq34936 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34930 eq82
    | exact resolve eq82 eq34930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq34930
  have eq34998 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq34936
    | exact resolve eq34936 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34936
  have eq37277 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31480 eq57
    | exact resolve eq57 eq31480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37298 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31480 eq4299
    | (have j0 := eq4299 (σ x)
       grind)
    | exact resolve eq4299 eq31480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31480
  have eq37312 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq37298
    | exact resolve eq37298 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37298
  have eq37313 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq37312
  have eq37322 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq37277
    | exact resolve eq37277 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37277
  have eq37475 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq37313
  have eq37691 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq37475 eq57
    | exact resolve eq57 eq37475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq37475
  have eq37745 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30 eq37691
    | exact resolve eq37691 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37691
  have eq37854 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4299 x
       have i₂ := eq34998
       grind)
    | exact superpose eq34998 eq4299
    | (have j0 := eq4299 x
       grind)
    | exact resolve eq4299 eq34998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4299
  have eq37873 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37854
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq37854
    | exact resolve eq37854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37854
  have eq37874 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq37873
  have eq37926 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq37322
       have i₂ := eq37745
       grind)
    | exact superpose eq37745 eq37322
    | exact resolve eq37322 eq37745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37322 eq37745
  have eq37952 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq37926
  have eq37983 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq37952 eq29
    | exact resolve eq29 eq37952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37952
  have eq41092 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq37874
  have eq41447 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34998
       have i₂ := eq41092
       grind)
    | exact superpose eq41092 eq34998
    | exact resolve eq34998 eq41092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34998 eq41092
  have eq41476 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq41447
  have eq41506 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq41476 eq31
    | exact resolve eq31 eq41476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq41476
  have eq41775 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq41506
    | exact resolve eq41506 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq41506
  have eq41776 : x = (M.op x y) ∨ x = y := by grind
  clear eq41775
  have eq41777 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq41776 eq22
    | exact resolve eq22 eq41776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41776
  have eq41983 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq41777
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41777
    | exact resolve eq41777 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41777
  have eq41984 : x = y := by
    first
    | (have r₁ := eq41983
       have r₂ := eq37983
       grind)
    | exact resolve eq41983 eq37983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37983 eq41983
  have eq41985 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq41984
       grind)
    | exact superpose eq41984 eq20
    | exact resolve eq20 eq41984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq41986 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq41984
       grind)
    | exact superpose eq41984 eq26
    | exact resolve eq26 eq41984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq42108 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30572
       have i₂ := eq41984
       grind)
    | exact superpose eq41984 eq30572
    | exact resolve eq30572 eq41984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30572
  have eq42189 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41986
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41986
    | exact resolve eq41986 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41986
  have eq42192 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq42189 eq28
    | exact resolve eq28 eq42189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq42578 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq44734 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq41984
       grind)
    | exact superpose eq41984 eq77
    | exact resolve eq77 eq41984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq44735 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44734
       have i₂ := eq41985
       grind)
    | exact superpose eq41985 eq44734
    | exact resolve eq44734 eq41985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44734
  have eq44736 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq42189 eq44735
    | exact resolve eq44735 eq42189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42189 eq44735
  have eq44737 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq44736
    | exact resolve eq44736 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44736
  have eq44738 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44737
       have i₂ := eq41985
       grind)
    | exact superpose eq41985 eq44737
    | exact resolve eq44737 eq41985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44737
  have eq44739 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq44738
       have i₂ := eq41984
       grind)
    | exact superpose eq41984 eq44738
    | exact resolve eq44738 eq41984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44738
  have eq44740 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq44739
       have i₂ := eq41984
       grind)
    | exact superpose eq41984 eq44739
    | exact resolve eq44739 eq41984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41984 eq44739
  have eq44741 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq44740
       have i₂ := eq41985
       grind)
    | exact superpose eq41985 eq44740
    | exact resolve eq44740 eq41985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41985 eq44740
  have eq44742 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq44741
  have eq44963 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq948 x
       have i₂ := eq42108
       grind)
    | exact superpose eq42108 eq948
    | (have j0 := eq948 x
       grind)
    | exact resolve eq948 eq42108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq42108
  have eq44986 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44963
  have eq45006 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44986
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44986
    | exact resolve eq44986 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44986
  have eq45027 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42192 eq45006
    | exact resolve eq45006 eq42192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42192 eq45006
  have eq45028 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45027
  have eq45053 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq45028 eq29
    | exact resolve eq29 eq45028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq45141 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq45028 eq42578
    | exact resolve eq42578 eq45028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42578 eq45028
  have eq45266 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45141 eq44742
    | exact resolve eq44742 eq45141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44742 eq45141
  have eq45307 : x = (M.op x y) := by
    first
    | (have r₁ := eq45266
       have r₂ := eq30634
       grind)
    | exact resolve eq45266 eq30634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30634 eq45266
  have eq45333 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq45307 eq22
    | exact resolve eq22 eq45307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45307
  have eq45589 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45333
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45333
    | exact resolve eq45333 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq45333
  have eq45664 : False := by grind
  exact eq45664

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_x_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
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
  have eq25 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq9 X1 (M.op x (M.op X1 x)) X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X1
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq9
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq38 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq39 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq65 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq50
    | exact resolve eq50 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq50
  have eq69 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq103 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq104 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq135 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X0 X0) X1
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq34
    | exact resolve eq34 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq104
    | (have j0 := eq104 (σ (k X0 X1)) (σ X1)
       grind)
    | exact resolve eq104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq331 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq326 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq326 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq326 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq326 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq326 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq371 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X1 X1
       have i₂ := eq331 X0 X1
       grind)
    | (have i₁ := eq27 X0 X1
       have i₂ := eq331 (M.op X1 X0) X1
       grind)
    | exact superpose eq331 eq27
    | (have j1 := eq331 X0 X1
       grind)
    | exact resolve eq27 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0
       have i₂ := eq371 X0 X1
       grind)
    | (have i₁ := eq25 X1
       have i₂ := eq371 X0 (M.op X1 X1)
       grind)
    | exact superpose eq371 eq25
    | (have j1 := eq371 X0 X1
       grind)
    | exact resolve eq25 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq371
  have eq580 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq498 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq498
    | (have j0 := eq498 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq498 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq582 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq498 X0 (τ (M.op (σ X0) (σ X0)))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq498
    | (have j0 := eq498 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq498 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq498
  have eq603 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq605 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq580 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq608 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq603 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq603
    | exact resolve eq603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq626 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq605 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq605
    | exact resolve eq605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq651 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq608 (M.op X0 X0)
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq608
    | exact resolve eq608 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq671 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq626 (M.op X0 X0)
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq626
    | exact resolve eq626 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq626
  have eq698 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq135 (τ X0) (τ (M.op X0 X0))
       have i₂ := eq651 X0
       grind)
    | exact superpose eq651 eq135
    | exact resolve eq135 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq698 X0
       have i₂ := eq651 X0
       grind)
    | exact superpose eq651 eq698
    | exact resolve eq698 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq698
  have eq705 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq703 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq703
    | exact resolve eq703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq756 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq705 X0
       grind)
    | exact superpose eq705 eq11
    | exact resolve eq11 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq992 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq756 X1
       grind)
    | exact superpose eq756 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq993 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq992 X0 X1
       have i₂ := eq756 X1
       grind)
    | exact superpose eq756 eq992
    | (have j0 := eq992 X0 X1
       grind)
    | exact resolve eq992 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1114 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq993 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq9505 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq283 X0 X1
       have i₂ := eq756 X1
       grind)
    | exact superpose eq756 eq283
    | (have j0 := eq283 X0 X1
       grind)
    | exact resolve eq283 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq9506 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9505 X0 X1
       have i₂ := eq756 X1
       grind)
    | exact superpose eq756 eq9505
    | (have j0 := eq9505 X0 X1
       grind)
    | exact resolve eq9505 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq9505
  have eq9507 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq9506 X0 X1
       have j1 := eq1114 X0 X1
       grind)
    | (have r₁ := eq9506 (k X0 X1) X1
       have r₂ := eq1114 X0 X1
       grind)
    | (have r₁ := eq9506 X0 X1
       have r₂ := eq1114 X0 X1
       grind)
    | exact resolve eq9506 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq9506
  have eq9662 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq9507 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq9507 X0 X1
       grind)
    | exact superpose eq9507 eq10
    | (have j1 := eq9507 X0 X1
       grind)
    | exact resolve eq10 eq9507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9507
  have eq9757 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9662 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9662
    | (have j0 := eq9662 X0 X1
       grind)
    | exact resolve eq9662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9662
  have eq9908 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9757 x y
       grind)
    | exact superpose eq9757 eq16
    | (have j1 := eq9757 x y
       grind)
    | exact resolve eq16 eq9757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9757
  have eq9968 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9908
       have i₂ := eq331 x y
       grind)
    | exact superpose eq331 eq9908
    | (have j1 := eq331 x y
       grind)
    | exact resolve eq9908 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq9908
  have eq9987 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq9968
  have eq9988 : x = (M.op y y) := by grind
  clear eq9987
  have eq10003 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq671 y
       have i₂ := eq9988
       grind)
    | exact superpose eq9988 eq671
    | exact resolve eq671 eq9988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq10026 : x = (M.op x y) := by
    first
    | (have i₁ := eq135 y y
       have i₂ := eq9988
       grind)
    | exact superpose eq9988 eq135
    | exact resolve eq135 eq9988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq9988
  have eq11000 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10003
       grind)
    | exact superpose eq10003 eq16
    | exact resolve eq16 eq10003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10003
  have eq11069 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11000
       have i₂ := eq10026
       grind)
    | exact superpose eq10026 eq11000
    | exact resolve eq11000 eq10026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10026 eq11000
  have eq11070 : False := by grind
  exact eq11070

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (k (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq77 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq84 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq77
  have eq91 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq138 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq139 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq138
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq138
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq156 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq139 eq16
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq163
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq163
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq201
  have eq256 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq263 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq296 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq325 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq260 (τ X0)
       grind)
    | exact superpose eq260 eq39
    | exact resolve eq39 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq342 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq325 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq325
    | exact resolve eq325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq402 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq67
    | exact resolve eq67 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq413 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq402 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq402
    | (have j0 := eq402 y x
       grind)
    | exact resolve eq402 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq402
    | (have j0 := eq402 (σ y) (σ x)
       grind)
    | exact resolve eq402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 X0
       have i₂ := eq402 X0 X2
       grind)
    | exact superpose eq402 eq14
    | exact resolve eq14 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X1 X2
       have i₂ := eq260 X0
       grind)
    | exact superpose eq260 eq69
    | exact resolve eq69 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq471 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq296 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq296
    | (have j0 := eq296 X0 y
       grind)
    | exact resolve eq296 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq296
    | (have j0 := eq296 X0 (M.op x y)
       grind)
    | exact resolve eq296 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq517 : (k (k y x) y) = (τ (k (k (σ y) (σ x)) (σ y))) := by
    first
    | exact superpose eq101 eq471
    | exact resolve eq471 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq456 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq14 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq456
    | exact resolve eq456 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq51 eq456
    | exact resolve eq456 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq538 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1 X0
       have i₂ := eq402 X0 X0
       grind)
    | exact superpose eq402 eq456
    | exact resolve eq456 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : (k (k (M.op x y) (M.op x y)) (M.op x y)) = (τ (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | exact superpose eq163 eq472
    | exact resolve eq472 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq611 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    by_contra hcon
    push Not at hcon
    have f624_12 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
      intro X0 X1 X2 X3
      grind
    have f624_19 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
      intro X0 X1 X2
      grind
    have f624_22 : (M.op X1 X0) ≠ (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by grind
    have f624_130 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
      intro X0 X1 X2 X3 X4
      first
      | (have i₁ := f624_19 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
         have i₂ := f624_12 X1 X4 X0 X2
         grind)
      | exact superpose f624_12 f624_19
      | exact resolve f624_19 f624_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f624_503 : (M.op X1 X0) ≠ (M.op X1 X0) := by
      first
      | (have i₁ := f624_22
         have i₂ := f624_130 X2 X0 X3 X4 X1
         grind)
      | exact superpose f624_130 f624_22
      | (have r₁ := f624_22
         have r₂ := f624_130 X2 X0 X3 X4 X1
         grind)
      | exact resolve f624_22 f624_130
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f624_518 : False := by grind
    exact f624_518
  have eq628 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq653 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq456 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq53 X1 X1 X0 X2
       grind)
    | exact superpose eq53 eq456
    | exact resolve eq456 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq456
  have eq843 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq54
    | (have j1 := eq73 X0 X0
       grind)
    | exact resolve eq54 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq857 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq856 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq864 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1065 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op y y))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq413 eq653
    | exact resolve eq653 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (M.op (σ y) (σ y)))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq415 eq653
    | exact resolve eq653 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1086 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq653 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq653
    | exact resolve eq653 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1144 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1086 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq1086
    | exact resolve eq1086 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1157 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1086 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1086
    | (have j0 := eq1086 x y
       grind)
    | exact resolve eq1086 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq256 eq1086
    | exact resolve eq1086 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq257 eq1086
    | exact resolve eq1086 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq1266 : (M.op x y) = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq1159 eq54
    | exact resolve eq54 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1267 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1159 eq56
    | exact resolve eq56 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1348 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1162 eq54
    | exact resolve eq54 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3173 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (M.op (M.op X1 (M.op X0 x)) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq534 eq532
    | exact resolve eq532 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq534
  have eq3289 : ∀ X0 X1 : G, (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (M.op (M.op X1 (M.op X0 x)) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1159 eq3173
    | exact resolve eq3173 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq3309 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X1 (M.op X0 x)) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1267 eq3289
    | exact resolve eq3289 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq3592 : (M.op x y) = (M.op x (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq3309 x x
       have i₂ := eq54 x
       grind)
    | exact superpose eq54 eq3309
    | exact resolve eq3309 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq3663 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq857 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq857
    | (have j0 := eq857 (τ X0)
       grind)
    | exact resolve eq857 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq3671 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3663 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3663
    | (have j0 := eq3663 X0
       grind)
    | exact resolve eq3663 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663
  have eq3677 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3671 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3671
    | (have j0 := eq3671 X0
       grind)
    | exact resolve eq3671 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671
  have eq3694 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 X0 X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq421
    | exact resolve eq421 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq3984 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq628 X0 sF4 sF4
       have i₂ := eq54 sF4
       grind)
    | exact superpose eq54 eq628
    | exact resolve eq628 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq4241 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq864 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq864
    | (have j0 := eq864 (τ X0)
       grind)
    | exact resolve eq864 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4267 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4241 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4241
    | (have j0 := eq4241 X0
       grind)
    | exact resolve eq4241 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4241
  have eq4278 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4267 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4267
    | (have j0 := eq4267 X0
       grind)
    | exact resolve eq4267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4267
  have eq4425 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq611 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq611
    | exact resolve eq611 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq611
  have eq4750 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) = (M.op (M.op X1 (M.op X2 (M.op y y))) (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq413 eq624
    | exact resolve eq624 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4759 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq415 eq624
    | exact resolve eq624 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq20463 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op y y))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1159 eq1065
    | exact resolve eq1065 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq20464 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op (σ y) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1162 eq1068
    | exact resolve eq1068 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq24776 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1144 X0 y
       have i₂ := eq4425 X0
       grind)
    | exact superpose eq4425 eq1144
    | exact resolve eq1144 eq4425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4425
  have eq24782 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3694 X0 X1
       have i₂ := eq1144 X0 X1
       grind)
    | exact superpose eq1144 eq3694
    | exact resolve eq3694 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3694
  have eq24801 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq3984 x
       have i₂ := eq1144 sF2 x
       grind)
    | exact superpose eq1144 eq3984
    | exact resolve eq3984 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984
  have eq26487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq26487
    | exact resolve eq26487 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26487
  have eq26501 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq26488
       have r₂ := eq28
       grind)
    | exact resolve eq26488 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26488
  have eq26517 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26501 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26501
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq26501
       grind)
    | exact resolve eq12 eq26501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26501
  have eq26539 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26517
  have eq26540 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26539
  have eq26562 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26540 eq103
    | exact resolve eq103 eq26540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26540
  have eq26575 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq26562
  have eq26599 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26575 eq54
    | exact resolve eq54 eq26575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26601 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26575 eq260
    | exact resolve eq260 eq26575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26575
  have eq26647 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq26599
    | exact resolve eq26599 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26599
  have eq26672 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq402 x y
       have i₂ := eq26647
       grind)
    | exact superpose eq26647 eq402
    | exact resolve eq402 eq26647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq28033 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26601 eq103
    | exact resolve eq103 eq26601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq26601
  have eq28051 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq28033
  have eq28079 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq28051
       grind)
    | exact superpose eq28051 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq28051
       grind)
    | exact resolve eq12 eq28051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28051
  have eq28101 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq28079
  have eq28102 : y = (k y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq28101
  have eq28410 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq28102
       grind)
    | exact superpose eq28102 eq91
    | exact resolve eq91 eq28102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28438 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28410
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28410
    | exact resolve eq28410 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28410
  have eq33698 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26647
       have i₂ := eq26672
       grind)
    | exact superpose eq26672 eq26647
    | exact resolve eq26647 eq26672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26647 eq26672
  have eq33750 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq33698
  have eq34527 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq33750
       grind)
    | exact superpose eq33750 eq84
    | exact resolve eq84 eq33750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq34537 : (M.op y y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  have eq34538 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq33750
       grind)
    | exact superpose eq33750 eq54
    | exact resolve eq54 eq33750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34540 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq260 x
       have i₂ := eq33750
       grind)
    | exact superpose eq33750 eq260
    | exact resolve eq260 eq33750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34570 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1144 x x
       have i₂ := eq33750
       grind)
    | exact superpose eq33750 eq1144
    | exact resolve eq1144 eq33750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33750
  have eq34589 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq34570
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34570
    | exact resolve eq34570 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34570
  have eq34602 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq34538
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34538
    | exact resolve eq34538 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34538
  have eq34606 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq34527
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34527
    | exact resolve eq34527 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34527
  have eq34608 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34602 eq28
    | exact resolve eq28 eq34602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34614 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34602 eq415
    | exact resolve eq415 eq34602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34669 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq34614
    | exact resolve eq34614 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34614
  have eq34674 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq34540
       grind)
    | exact superpose eq34540 eq91
    | exact resolve eq91 eq34540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34540
  have eq34707 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq34674
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34674
    | exact resolve eq34674 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34674
  have eq35279 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34669 eq54
    | exact resolve eq54 eq34669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35282 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34669 eq263
    | exact resolve eq263 eq34669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34669
  have eq35632 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34602 eq35279
    | exact resolve eq35279 eq34602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35279
  have eq35701 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq35632
  have eq35841 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34602 eq35282
    | exact resolve eq35282 eq34602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35282
  have eq35850 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq35841
  have eq36184 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq35701 eq24782
    | exact resolve eq24782 eq35701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24782 eq35701
  have eq36189 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq36184
    | exact resolve eq36184 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36184
  have eq36773 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq35850 eq28438
    | exact resolve eq28438 eq35850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28438
  have eq36781 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq36773
  have eq36786 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36781
       have r₂ := eq34608
       grind)
    | exact resolve eq36781 eq34608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36781
  have eq36798 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34602 eq36189
    | exact resolve eq36189 eq34602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36189
  have eq36846 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq36798
  have eq36978 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  have eq37262 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq34537
       grind)
    | exact superpose eq34537 eq91
    | exact resolve eq91 eq34537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34537
  have eq47734 : (k (k y x) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq36978 eq517
    | exact resolve eq517 eq36978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq36978
  have eq47766 : (τ (σ y)) = (k (k y x) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq47734
       have i₂ := eq260 sF3
       grind)
    | exact superpose eq260 eq47734
    | exact resolve eq47734 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47734
  have eq47768 : y = (k (k y x) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq47766
    | exact resolve eq47766 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47766
  have eq49068 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34606 eq50
    | exact resolve eq50 eq34606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49089 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34606 eq4278
    | (have j0 := eq4278 (σ x)
       grind)
    | exact resolve eq4278 eq34606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278 eq34606
  have eq49104 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq49089
    | exact resolve eq49089 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49089
  have eq49105 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq49104
  have eq49114 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq49068
    | exact resolve eq49068 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49068
  have eq49270 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq37262
       have i₂ := eq34589
       grind)
    | exact superpose eq34589 eq37262
    | exact resolve eq37262 eq34589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34589 eq37262
  have eq49352 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq49270
  have eq49363 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq49352
    | exact resolve eq49352 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49352
  have eq49387 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq49363 eq34707
    | exact resolve eq34707 eq49363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34707 eq49363
  have eq49402 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq49387
  have eq49437 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq49402 eq415
    | exact resolve eq415 eq49402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49402
  have eq49528 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq49437
    | exact resolve eq49437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49437
  have eq49651 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq49528
  have eq49754 : (k (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1162 eq49651
    | exact resolve eq49651 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49651
  have eq51428 : (M.op x y) = (M.op x x) ∨ (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1157 eq143
    | exact resolve eq143 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq51429 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq51428
  have eq57121 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq49105 eq260
    | exact resolve eq260 eq49105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49105
  have eq58525 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq57121 eq50
    | exact resolve eq50 eq57121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57121
  have eq58574 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq58525
    | exact resolve eq58525 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58525
  have eq59423 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq49114
       have i₂ := eq58574
       grind)
    | exact superpose eq58574 eq49114
    | exact resolve eq49114 eq58574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49114 eq58574
  have eq59444 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq59423
  have eq59471 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59444 eq28
    | exact resolve eq28 eq59444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59477 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59444 eq415
    | exact resolve eq415 eq59444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59599 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq59477
    | exact resolve eq59477 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59477
  have eq59914 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59599 eq263
    | exact resolve eq263 eq59599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59599
  have eq60487 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59444 eq59914
    | exact resolve eq59914 eq59444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59444 eq59914
  have eq60502 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq60487
  have eq62338 : (τ (σ x)) = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq60502 eq101
    | exact resolve eq101 eq60502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60502
  have eq62383 : x = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq62338
    | exact resolve eq62338 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62338
  have eq62857 : x = y ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28102
       have i₂ := eq62383
       grind)
    | exact superpose eq62383 eq28102
    | exact resolve eq28102 eq62383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28102 eq62383
  have eq62875 : x = y ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq62857
  have eq62885 : y = (M.op x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq62875
       have r₂ := eq59471
       grind)
    | exact resolve eq62875 eq59471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62875
  have eq63054 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq62885
       grind)
    | exact superpose eq62885 eq54
    | exact resolve eq54 eq62885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62885
  have eq63146 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63054
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq63054
    | exact resolve eq63054 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63054
  have eq63428 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63146 eq30
    | exact resolve eq30 eq63146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63441 : (k y y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63146 eq109
    | exact resolve eq109 eq63146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq63444 : (k y (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63146 eq124
    | exact resolve eq124 eq63146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq63448 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63146 eq156
    | exact resolve eq156 eq63146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq63496 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63146 eq1348
    | exact resolve eq1348 eq63146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63146
  have eq63601 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq163 eq63448
    | exact resolve eq63448 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63448
  have eq63604 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq163 eq63444
    | exact resolve eq63444 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63444
  have eq63607 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq163 eq63441
    | exact resolve eq63441 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63441
  have eq63618 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq63428
    | exact resolve eq63428 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63428
  have eq63693 : (M.op x x) = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63618 eq1157
    | exact resolve eq1157 eq63618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq77954 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63601 eq140
    | exact resolve eq140 eq63601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78007 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq139 eq77954
    | exact resolve eq77954 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77954
  have eq78419 : (k y y) = (k (M.op x y) y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63607 eq63601
    | exact resolve eq63601 eq63607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63601
  have eq78420 : (k y y) = (k y (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63607 eq63604
    | exact resolve eq63604 eq63607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63604 eq63607
  have eq78439 : (k y y) = (k y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq78420
  have eq78440 : (k y y) = (k (M.op x y) y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq78419
  have eq82903 : (M.op x (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24776 x
       have i₂ := eq63693
       grind)
    | exact superpose eq63693 eq24776
    | exact resolve eq24776 eq63693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24776 eq63693
  have eq82981 : x = (M.op (M.op x y) (M.op x x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82903
       have i₂ := eq54 x
       grind)
    | exact superpose eq54 eq82903
    | exact resolve eq82903 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82903
  have eq88567 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63618 eq82981
    | exact resolve eq82981 eq63618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88606 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq82981 eq1086
    | exact resolve eq1086 eq82981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82981
  have eq88640 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq88567
  have eq88652 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1159 eq88606
    | exact resolve eq88606 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88606
  have eq89218 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1086 y (M.op x x)
       have i₂ := eq88640
       grind)
    | exact superpose eq88640 eq1086
    | exact resolve eq1086 eq88640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88640
  have eq89261 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89218
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89218
    | exact resolve eq89218 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89218
  have eq89319 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) y) ∨ x = y ∨ x = (M.op x y) := by grind
  have eq89322 : y = (k (M.op x y) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq260 y
       have i₂ := eq89261
       grind)
    | exact superpose eq89261 eq260
    | exact resolve eq260 eq89261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89323 : (M.op x y) = (k y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq263 y
       have i₂ := eq89261
       grind)
    | exact superpose eq89261 eq263
    | exact resolve eq263 eq89261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq89261
  have eq89420 : (M.op y (M.op x y)) = (k (M.op x y) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1159 eq89319
    | exact resolve eq89319 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89319
  have eq89580 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq89322 eq139
    | exact resolve eq139 eq89322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq89597 : y = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq89322 eq78440
    | exact resolve eq78440 eq89322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89322
  have eq89607 : y = (k y y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq89597
  have eq89627 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89580
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq89580
    | exact resolve eq89580 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89580
  have eq89661 : (M.op x y) = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq89323 eq78439
    | exact resolve eq78439 eq89323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78439 eq89323
  have eq89669 : (M.op x y) = (k y y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq89661
  have eq89985 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq864 y
       have i₂ := eq89607
       grind)
    | exact superpose eq89607 eq864
    | (have j0 := eq864 y
       grind)
    | exact resolve eq864 eq89607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq89607
  have eq90001 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq89985
  have eq90015 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90001
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq90001
    | exact resolve eq90001 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90001
  have eq90130 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq89627 eq78007
    | exact resolve eq78007 eq89627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78007 eq89627
  have eq90140 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq90130
  have eq90158 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq89669
       grind)
    | exact superpose eq89669 eq92
    | exact resolve eq92 eq89669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq89669
  have eq90219 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq90158
    | exact resolve eq90158 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90158
  have eq90326 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq90015
  have eq90576 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq90140 eq163
    | exact resolve eq163 eq90140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90140
  have eq90620 : y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq90576
    | exact resolve eq90576 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90576
  have eq92336 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq90620 eq3677
    | (have j0 := eq3677 (M.op x y)
       grind)
    | exact resolve eq3677 eq90620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3677 eq90620
  have eq92364 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq92336
       have r₂ := eq63618
       grind)
    | exact resolve eq92336 eq63618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92336
  have eq92386 : (M.op x y) = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1159 eq92364
    | exact resolve eq92364 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92364
  have eq94094 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq92386 eq3592
    | exact resolve eq3592 eq92386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592 eq92386
  have eq95197 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq88652 eq1266
    | exact resolve eq1266 eq88652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq96870 : (M.op y y) = (k y y) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63618 eq89420
    | exact resolve eq89420 eq63618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96901 : (k y y) = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq89420 eq78440
    | exact resolve eq78440 eq89420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78440 eq89420
  have eq96913 : (k y y) = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq96901
  have eq96921 : (M.op y y) = (k y y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq96870
  have eq97426 : (M.op y y) = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96913
       have i₂ := eq96921
       grind)
    | exact superpose eq96921 eq96913
    | exact resolve eq96913 eq96921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96913 eq96921
  have eq97443 : (M.op y y) = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq97426
  have eq97594 : (M.op y y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq97443 eq88652
    | exact resolve eq88652 eq97443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88652
  have eq97673 : (M.op y y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq97594
  have eq97860 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq90326 eq90219
    | exact resolve eq90219 eq90326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90219 eq90326
  have eq97881 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq97860
  have eq97962 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq97881 eq538
    | exact resolve eq538 eq97881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq97881
  have eq99113 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq256
       have i₂ := eq97673
       grind)
    | exact superpose eq97673 eq256
    | exact resolve eq256 eq97673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq97673
  have eq116026 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq36786
       grind)
    | exact superpose eq36786 eq54
    | exact resolve eq54 eq36786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36786
  have eq116124 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq116026
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116026
    | exact resolve eq116026 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116026
  have eq116125 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq116124
  have eq116667 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq116125 eq27
    | exact resolve eq27 eq116125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116825 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq116125 eq35850
    | exact resolve eq35850 eq116125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35850
  have eq116849 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq116125 eq49754
    | exact resolve eq49754 eq116125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49754
  have eq117019 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq116849
  have eq117039 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq116825
  have eq117067 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq117019
       have r₂ := eq34608
       grind)
    | exact resolve eq117019 eq34608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117019
  have eq117081 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq117039
       have r₂ := eq34608
       grind)
    | exact resolve eq117039 eq34608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117039
  have eq117186 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq116667 eq36846
    | exact resolve eq36846 eq116667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36846 eq116667
  have eq117296 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq117186
  have eq118294 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq117081 eq50
    | exact resolve eq50 eq117081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117081
  have eq118351 : x = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq118294
    | exact resolve eq118294 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq118294
  have eq124584 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq118351
       grind)
    | exact superpose eq118351 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq118351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118351
  have eq124585 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq124584
  have eq126188 : (k x x) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq124585
  have eq131260 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq117296 eq117067
    | exact resolve eq117067 eq117296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117067 eq117296
  have eq131278 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq131260
  have eq131282 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq131278
    | exact resolve eq131278 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131278
  have eq131301 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq131282 eq101
    | exact resolve eq101 eq131282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq131282
  have eq131456 : y = (k (τ (M.op (σ x) (σ y))) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq47768
       have i₂ := eq131301
       grind)
    | exact superpose eq131301 eq47768
    | exact resolve eq47768 eq131301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47768 eq131301
  have eq131475 : y = (k (τ (M.op (σ x) (σ y))) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq131456
  have eq131499 : y = (τ (k (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq131475
       have i₂ := eq471 sF4
       grind)
    | exact superpose eq471 eq131475
    | exact resolve eq131475 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq131475
  have eq132495 : y = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq116125 eq131499
    | exact resolve eq131499 eq116125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116125 eq131499
  have eq132710 : y = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq132495
  have eq132721 : y = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq132710
       have r₂ := eq34608
       grind)
    | exact resolve eq132710 eq34608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34608 eq132710
  have eq133594 : y = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34602 eq132721
    | exact resolve eq132721 eq34602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34602 eq132721
  have eq133801 : y = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq133594
  have eq133811 : y = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq50 eq133801
    | exact resolve eq133801 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq133801
  have eq148599 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq133811
       have i₂ := eq126188
       grind)
    | exact superpose eq126188 eq133811
    | exact resolve eq133811 eq126188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126188 eq133811
  have eq148622 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq148599
  have eq148689 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq148622
       grind)
    | exact superpose eq148622 eq54
    | exact resolve eq54 eq148622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148622
  have eq148797 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq148689
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq148689
    | exact resolve eq148689 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148689
  have eq148798 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq148797
  have eq148810 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148798 eq27
    | exact resolve eq27 eq148798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148811 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148798 eq30
    | exact resolve eq30 eq148798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148812 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq148798 eq37
    | exact resolve eq37 eq148798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq148813 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq148798 eq41
    | exact resolve eq41 eq148798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq149106 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq42 eq148813
    | exact resolve eq148813 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148813
  have eq149107 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq148812
    | exact resolve eq148812 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq148812
  have eq149108 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq148811
    | exact resolve eq148811 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148811
  have eq149375 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq149108
  have eq149561 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148810 eq97962
    | exact resolve eq97962 eq148810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97962
  have eq149619 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq149561
  have eq149641 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq149619
       have r₂ := eq149375
       grind)
    | exact resolve eq149619 eq149375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149619
  have eq149644 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq415 eq149641
    | exact resolve eq149641 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq149641
  have eq149645 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148798 eq149644
    | exact resolve eq149644 eq148798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149716 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149644 eq260
    | exact resolve eq260 eq149644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149644
  have eq149814 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq149645
  have eq150040 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148798 eq149716
    | exact resolve eq149716 eq148798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149716
  have eq150089 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq150040
  have eq152316 : (τ (k (σ (M.op x y)) (σ (M.op x y)))) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq150089 eq582
    | exact resolve eq582 eq150089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq150089
  have eq152373 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq163 eq152316
    | exact resolve eq152316 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152316
  have eq152837 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x y)) = (M.op (M.op X1 (M.op X2 (M.op y y))) (M.op (M.op x y) (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4750 X1 X1 X2
       have i₂ := eq1144 sF0 X1
       grind)
    | exact superpose eq1144 eq4750
    | exact resolve eq4750 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4750
  have eq153239 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op y y))) y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq99113 eq152837
    | exact resolve eq152837 eq99113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99113
  have eq153240 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op y y))) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq95197 eq152837
    | exact resolve eq152837 eq95197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95197 eq152837
  have eq153389 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op y y))) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq153240 X0 X1
       grind)
    | (have r₁ := eq153240 X0 X1
       have r₂ := eq149375
       grind)
    | exact resolve eq153240 eq149375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153240
  have eq153390 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op y y))) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq153239 X0 X1
       grind)
    | (have r₁ := eq153239 X0 X1
       have r₂ := eq149375
       grind)
    | exact resolve eq153239 eq149375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153239
  have eq153423 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20463 eq153389
    | exact resolve eq153389 eq20463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20463 eq153389
  have eq153424 : (M.op y y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq153390 x x
       have i₂ := eq653 x y y x
       grind)
    | exact superpose eq653 eq153390
    | exact resolve eq153390 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq153390
  have eq153442 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4759 X1 X1 X2
       have i₂ := eq1144 sF4 X1
       grind)
    | exact superpose eq1144 eq4759
    | exact resolve eq4759 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144 eq4759
  have eq153677 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op (σ y) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq63496 eq153442
    | exact resolve eq153442 eq63496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63496 eq153442
  have eq153828 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op (σ y) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq153677 X0 X1
       grind)
    | (have r₁ := eq153677 X0 X1
       have r₂ := eq149375
       grind)
    | exact resolve eq153677 eq149375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153677
  have eq153854 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20464 eq153828
    | exact resolve eq153828 eq20464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20464 eq153828
  have eq159270 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq153854 eq1348
    | exact resolve eq1348 eq153854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153854
  have eq159446 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq159270 eq14
    | exact resolve eq14 eq159270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159270
  have eq160300 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq149814 eq159446
    | exact resolve eq159446 eq149814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149814 eq159446
  have eq160395 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq160300
  have eq164991 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq153423 eq1267
    | exact resolve eq1267 eq153423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq153423
  have eq229650 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq149106 eq35
    | exact resolve eq35 eq149106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149106
  have eq229987 : ∀ X0 : G, (σ (k (τ X0) y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq229650
    | (have j0 := eq229650 X0
       grind)
    | exact resolve eq229650 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229650
  have eq230081 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq229987 X0
       have i₂ := eq35 X0 y
       grind)
    | exact superpose eq35 eq229987
    | exact resolve eq229987 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq229987
  have eq230135 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq230081 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq230081
    | (have j0 := eq230081 X0
       grind)
    | exact resolve eq230081 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230081
  have eq231267 : (σ y) = (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq230135 eq342
    | exact resolve eq342 eq230135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq230135
  have eq231602 : (σ y) = (σ (k (M.op (τ (σ y)) (τ (σ y))) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq231267
    | exact resolve eq231267 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq231267
  have eq231685 : (σ y) = (σ (k (M.op y y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq231602
    | exact resolve eq231602 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231602
  have eq275005 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq164991
  have eq275174 : (M.op y (M.op x y)) = (k (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1159 eq275005
    | exact resolve eq275005 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159 eq275005
  have eq292022 : (M.op y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq94094 eq275174
    | exact resolve eq275174 eq94094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94094 eq275174
  have eq292048 : (M.op y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq292022
  have eq292056 : (M.op y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq292048
       have r₂ := eq149375
       grind)
    | exact resolve eq292048 eq149375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292048
  have eq292087 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq292056 eq140
    | exact resolve eq140 eq292056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq292056
  have eq292270 : (σ (M.op y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq97443 eq292087
    | exact resolve eq292087 eq97443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97443 eq292087
  have eq292430 : (σ (M.op y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq292270
  have eq292446 : (σ (M.op y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq292430
       have r₂ := eq149375
       grind)
    | exact resolve eq292430 eq149375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292430
  have eq293743 : (M.op y y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq292446
       grind)
    | exact superpose eq292446 eq16
    | exact resolve eq16 eq292446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292446
  have eq293895 : (M.op y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq163 eq293743
    | exact resolve eq293743 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq293743
  have eq422814 : (M.op y y) = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq293895 eq152373
    | exact resolve eq152373 eq293895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152373 eq293895
  have eq422869 : (M.op y y) = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq422814
  have eq484181 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq422869 eq231685
    | exact resolve eq231685 eq422869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231685 eq422869
  have eq484206 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq484181
  have eq485502 : (σ y) = (σ (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq484206
       have i₂ := eq153424
       grind)
    | exact superpose eq153424 eq484206
    | exact resolve eq484206 eq153424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153424 eq484206
  have eq485716 : (σ y) = (σ (M.op x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq485502
  have eq485747 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq51429 eq485716
    | exact resolve eq485716 eq51429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51429 eq485716
  have eq1017277 : (τ (σ y)) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq485747 eq149
    | exact resolve eq149 eq485747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485747
  have eq1017340 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq1017277
    | exact resolve eq1017277 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017277
  have eq1106879 : y = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq1017340
       grind)
    | exact superpose eq1017340 eq54
    | exact resolve eq54 eq1017340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1017340
  have eq1132454 : y = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq63618 eq1106879
    | exact resolve eq1106879 eq63618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63618 eq1106879
  have eq1132570 : y = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1132454
  have eq1132661 : y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1132570
       have r₂ := eq149375
       grind)
    | exact resolve eq1132570 eq149375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149375 eq1132570
  have eq1132730 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1132661
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1132661
    | exact resolve eq1132661 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132661
  have eq1132731 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1132730
  have eq1134220 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq1132731
       grind)
    | exact superpose eq1132731 eq91
    | exact resolve eq91 eq1132731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132731
  have eq1134406 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1134220
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1134220
    | exact resolve eq1134220 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134220
  have eq1134595 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148798 eq1134406
    | exact resolve eq1134406 eq148798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134406
  have eq1134714 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1134595
  have eq1136119 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1134714 eq149
    | exact resolve eq149 eq1134714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq1134714
  have eq1136184 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1136119
    | exact resolve eq1136119 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136119
  have eq1136694 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1136184 eq149107
    | exact resolve eq149107 eq1136184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149107 eq1136184
  have eq1136738 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq1136694
  have eq1136783 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1136738
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq1136738
    | exact resolve eq1136738 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1136738
  have eq1136855 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq1136783
    | exact resolve eq1136783 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136783
  have eq1137547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1136855 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1136855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136855
  have eq1137614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq1137547
    | exact resolve eq1137547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137547
  have eq1137627 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1137614
       have r₂ := eq28
       grind)
    | exact resolve eq1137614 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137614
  have eq1254816 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148798 eq1137627
    | exact resolve eq1137627 eq148798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148798 eq1137627
  have eq1255067 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1254816
  have eq1263835 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1255067 eq1086
    | exact resolve eq1086 eq1255067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq1255067
  have eq1263955 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1263835
  have eq1264023 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1263955 eq24801
    | exact resolve eq24801 eq1263955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24801 eq1263955
  have eq1264221 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq148810 eq1264023
    | exact resolve eq1264023 eq148810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148810 eq1264023
  have eq1264433 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq1264221
  have eq1264504 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1162 eq1264433
    | exact resolve eq1264433 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq1264433
  have eq1264536 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1264504 eq1348
    | exact resolve eq1348 eq1264504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348 eq1264504
  have eq1264916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1264536 eq160395
    | exact resolve eq160395 eq1264536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160395 eq1264536
  have eq1265116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1264916
  have eq1265187 : x = (M.op x y) := by
    first
    | (have r₁ := eq1265116
       have r₂ := eq28
       grind)
    | exact resolve eq1265116 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265116
  have eq1266247 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1265187 eq21
    | exact resolve eq21 eq1265187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1266300 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1265187 eq413
    | exact resolve eq413 eq1265187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq1266712 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1266300
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1266300
    | exact resolve eq1266300 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1266300
  have eq1266760 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1266247
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1266247
    | exact resolve eq1266247 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266247
  have eq1266762 : x = (M.op y y) := by
    first
    | exact superpose eq1265187 eq1266712
    | exact resolve eq1266712 eq1265187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266712
  have eq1266764 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1266760 eq27
    | exact resolve eq27 eq1266760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1266980 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1266760 eq59471
    | (have r₁ := eq59471
       have r₂ := eq1266760
       grind)
    | exact resolve eq59471 eq1266760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59471
  have eq1267208 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1266980
  have eq1267471 : y = (k x y) := by
    first
    | (have i₁ := eq260 y
       have i₂ := eq1266762
       grind)
    | exact superpose eq1266762 eq260
    | exact resolve eq260 eq1266762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq1266762
  have eq1276042 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1267208 eq30
    | exact resolve eq30 eq1267208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1267208
  have eq1276943 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1276042
    | exact resolve eq1276042 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1276042
  have eq1277045 : x = y ∨ x = y := by
    first
    | exact superpose eq1265187 eq1276943
    | exact resolve eq1276943 eq1265187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276943
  have eq1277046 : x = y := by grind
  clear eq1277045
  have eq1277147 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1277046
       grind)
    | exact superpose eq1277046 eq25
    | exact resolve eq25 eq1277046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1277952 : x = (k x x) := by
    first
    | (have i₁ := eq1267471
       have i₂ := eq1277046
       grind)
    | exact superpose eq1277046 eq1267471
    | exact resolve eq1267471 eq1277046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267471 eq1277046
  have eq1278203 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1277147
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1277147
    | exact resolve eq1277147 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277147
  have eq1278418 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1266760 eq1278203
    | exact resolve eq1278203 eq1266760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278203
  have eq1279361 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1278418 eq1266764
    | exact resolve eq1266764 eq1278418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266764 eq1278418
  have eq1282095 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1279361 eq203
    | exact resolve eq203 eq1279361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq1279361
  have eq1282482 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq1282095
       have r₂ := eq28
       grind)
    | exact resolve eq1282095 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282095
  have eq1282510 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1265187 eq1282482
    | exact resolve eq1282482 eq1265187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265187 eq1282482
  have eq1282521 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1282510
       have i₂ := eq1277952
       grind)
    | exact superpose eq1277952 eq1282510
    | exact resolve eq1282510 eq1277952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277952 eq1282510
  have eq1282560 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1282521 eq15
    | exact resolve eq15 eq1282521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282521
  have eq1283354 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1282560
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1282560
    | exact resolve eq1282560 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1282560
  have eq1283581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1266760 eq1283354
    | exact resolve eq1283354 eq1266760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266760 eq1283354
  have eq1283704 : False := by grind
  exact eq1283704

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_y_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) ∨ (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq37
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq84
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq232 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52
    | (have j0 := eq52 y x
       grind)
    | exact resolve eq52 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y) (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq245 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq232 eq14
    | exact resolve eq14 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq272 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq233 eq14
    | exact resolve eq14 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq77
    | (have j0 := eq77 (σ X0)
       grind)
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq44
    | (have j1 := eq77 x
       grind)
    | exact resolve eq44 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq365 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq77 sF2
       grind)
    | exact superpose eq77 eq56
    | (have j1 := eq77 (σ x)
       grind)
    | exact resolve eq56 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq525 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq899 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq74
    | exact resolve eq74 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq3395 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq525
    | exact resolve eq525 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq3425 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3395
    | (have j0 := eq3395 (σ y) (σ x)
       grind)
    | exact resolve eq3395 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3395
  have eq3709 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq357 X0
       grind)
    | exact superpose eq357 eq50
    | (have j1 := eq357 X0
       grind)
    | exact resolve eq50 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3723 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq357 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq4098 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq528 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq528
    | exact resolve eq528 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq7887 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq899 X0 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq899
    | (have r₁ := eq899 X0 X0
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq899 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq7888 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7887
  have eq11467 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq245 eq238
    | exact resolve eq238 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq11471 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq272 eq238
    | exact resolve eq238 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq11582 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11467 eq238
    | exact resolve eq238 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11467
  have eq11607 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq11471 eq238
    | exact resolve eq238 eq11471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq11869 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq11582 y
       have i₂ := eq50 y
       grind)
    | exact superpose eq50 eq11582
    | exact resolve eq11582 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11582
  have eq12233 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11607 sF3
       have i₂ := eq50 sF3
       grind)
    | exact superpose eq50 eq11607
    | exact resolve eq11607 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11607
  have eq16792 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4098 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq4098
    | exact resolve eq4098 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4098
  have eq23590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23590
    | exact resolve eq23590 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23590
  have eq23602 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23591
       have r₂ := eq28
       grind)
    | exact resolve eq23591 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23591
  have eq23604 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23602
    | exact resolve eq23602 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23602
  have eq23620 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23604 eq50
    | exact resolve eq50 eq23604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23633 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23604 eq52
    | exact resolve eq52 eq23604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23604
  have eq23663 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12233 eq23633
    | exact resolve eq23633 eq12233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12233 eq23633
  have eq23749 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23620 eq50
    | exact resolve eq50 eq23620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23620
  have eq23786 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23749
    | exact resolve eq23749 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23749
  have eq24060 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23786 eq11471
    | exact resolve eq11471 eq23786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11471 eq23786
  have eq24091 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24060
    | exact resolve eq24060 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24060
  have eq24114 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24091 eq50
    | exact resolve eq50 eq24091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24091
  have eq25403 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23663 eq50
    | exact resolve eq50 eq23663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23663
  have eq25442 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25403
    | exact resolve eq25403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25403
  have eq25465 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25442 eq24114
    | exact resolve eq24114 eq25442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24114 eq25442
  have eq25508 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq25465
  have eq25556 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq25508
       grind)
    | exact superpose eq25508 eq52
    | exact resolve eq52 eq25508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25508
  have eq25588 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq11869 eq25556
    | exact resolve eq25556 eq11869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11869 eq25556
  have eq27053 : x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq25588
       grind)
    | exact superpose eq25588 eq52
    | exact resolve eq52 eq25588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25588
  have eq29600 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27053 eq16792
    | exact resolve eq16792 eq27053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16792
  have eq29605 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29600
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29600
    | exact resolve eq29600 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29600
  have eq31477 : y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq29605
       grind)
    | exact superpose eq29605 eq50
    | exact resolve eq50 eq29605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29605
  have eq32181 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31477 eq27053
    | exact resolve eq27053 eq31477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27053 eq31477
  have eq32235 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq32181
  have eq32302 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7888 y
       have i₂ := eq32235
       grind)
    | exact superpose eq32235 eq7888
    | exact resolve eq7888 eq32235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888
  have eq32308 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq32235
       grind)
    | exact superpose eq32235 eq52
    | exact resolve eq52 eq32235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq32235
  have eq32336 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq32302
  have eq32479 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq361
       have i₂ := eq32308
       grind)
    | exact superpose eq32308 eq361
    | exact resolve eq361 eq32308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32308
  have eq32541 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq32479
  have eq32548 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32541
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32541
    | exact resolve eq32541 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32541
  have eq76617 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3709 x
       have i₂ := eq32336
       grind)
    | exact superpose eq32336 eq3709
    | (have j0 := eq3709 x
       grind)
    | exact resolve eq3709 eq32336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709 eq32336
  have eq76706 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76617
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq76617
    | exact resolve eq76617 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76617
  have eq76730 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76706
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq76706
    | exact resolve eq76706 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76706
  have eq76743 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq76730
    | exact resolve eq76730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76730
  have eq76744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq76743
  have eq76751 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76744
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq76744
    | exact resolve eq76744 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76744
  have eq76787 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq76751
  have eq76878 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq76787 eq32548
    | exact resolve eq32548 eq76787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32548 eq76787
  have eq76893 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq76878
  have eq76911 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq76893 eq28
    | exact resolve eq28 eq76893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76915 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq76893 eq233
    | exact resolve eq233 eq76893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq76922 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq76893 eq3425
    | exact resolve eq3425 eq76893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3425
  have eq77042 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq76922
    | exact resolve eq76922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76922
  have eq77230 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq77042 eq239
    | exact resolve eq239 eq77042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq77429 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq76893 eq77230
    | exact resolve eq77230 eq76893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77230
  have eq77438 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq77429
  have eq78686 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq77438 eq97
    | exact resolve eq97 eq77438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq77438
  have eq78702 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq78686
       have r₂ := eq76911
       grind)
    | exact resolve eq78686 eq76911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78686
  have eq79249 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq77042 eq76915
    | exact resolve eq76915 eq77042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76915 eq77042
  have eq79298 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq79249
  have eq79769 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq76893 eq79298
    | exact resolve eq79298 eq76893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76893 eq79298
  have eq79840 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq79769
  have eq79851 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq79840 eq365
    | exact resolve eq365 eq79840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq79840
  have eq79928 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq79851
  have eq79935 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30 eq79928
    | exact resolve eq79928 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79928
  have eq80140 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79935
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq79935
    | (have j1 := eq77 x
       grind)
    | exact resolve eq79935 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79935
  have eq117353 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq80140
       grind)
    | exact superpose eq80140 eq50
    | exact resolve eq50 eq80140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq80140
  have eq117437 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117353
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq117353
    | exact resolve eq117353 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117353
  have eq117476 : x = (M.op x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78702
       have i₂ := eq117437
       grind)
    | exact superpose eq117437 eq78702
    | exact resolve eq78702 eq117437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78702 eq117437
  have eq117554 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq117476
  have eq117598 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq117554 eq30
    | exact resolve eq30 eq117554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117554
  have eq117800 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq117598
    | exact resolve eq117598 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq117598
  have eq117801 : x = (M.op x y) ∨ x = y := by grind
  clear eq117800
  have eq117802 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq117801 eq21
    | exact resolve eq21 eq117801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118213 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq117802
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq117802
    | exact resolve eq117802 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117802
  have eq118410 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq118213 eq76911
    | (have r₁ := eq76911
       have r₂ := eq118213
       grind)
    | exact resolve eq76911 eq118213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76911 eq118213
  have eq118573 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq118410
  have eq118574 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq118573
  have eq119098 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq118574 eq30
    | exact resolve eq30 eq118574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq118574
  have eq119571 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq119098
    | exact resolve eq119098 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq119098
  have eq119870 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq119571 eq117801
    | exact resolve eq117801 eq119571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117801 eq119571
  have eq119871 : x = y := by grind
  clear eq119870
  have eq120075 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq119871
       grind)
    | exact superpose eq119871 eq19
    | exact resolve eq19 eq119871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq120076 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq119871
       grind)
    | exact superpose eq119871 eq25
    | exact resolve eq25 eq119871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq119871
  have eq120504 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq120076
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq120076
    | exact resolve eq120076 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120076
  have eq120699 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq120504 eq27
    | exact resolve eq27 eq120504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq120504
  have eq120927 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq361
       have i₂ := eq120075
       grind)
    | exact superpose eq120075 eq361
    | exact resolve eq361 eq120075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq120971 : x = (k (M.op x y) x) := by grind
  clear eq120075
  have eq121039 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq120927
    | exact resolve eq120927 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120927
  have eq121125 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq127092 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121039 eq77
    | (have j0 := eq77 (σ x)
       grind)
    | exact resolve eq77 eq121039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq127104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120699 eq127092
    | exact resolve eq127092 eq120699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127092
  have eq127116 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127104
       have r₂ := eq28
       grind)
    | exact resolve eq127104 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127104
  have eq127122 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq120699 eq127116
    | exact resolve eq127116 eq120699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127116
  have eq127127 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127122 eq28
    | exact resolve eq28 eq127122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127257 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127122 eq121125
    | exact resolve eq121125 eq127122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121125 eq127122
  have eq133051 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127257 eq121039
    | exact resolve eq121039 eq127257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121039 eq127257
  have eq133066 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq133051
  have eq133087 : x = (M.op x y) := by
    first
    | (have r₁ := eq133066
       have r₂ := eq127127
       grind)
    | exact resolve eq133066 eq127127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127127 eq133066
  have eq133106 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq133087 eq21
    | exact resolve eq21 eq133087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq133365 : x = (k x x) := by
    first
    | exact superpose eq133087 eq120971
    | exact resolve eq120971 eq133087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120971 eq133087
  have eq133556 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq133106
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq133106
    | exact resolve eq133106 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133106
  have eq134276 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3723 x
       have i₂ := eq133365
       grind)
    | exact superpose eq133365 eq3723
    | (have j0 := eq3723 x
       grind)
    | exact resolve eq3723 eq133365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723 eq133365
  have eq134280 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq134276
  have eq134297 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq134280
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq134280
    | exact resolve eq134280 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq134280
  have eq134319 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120699 eq134297
    | exact resolve eq134297 eq120699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120699 eq134297
  have eq134338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq133556 eq134319
    | exact resolve eq134319 eq133556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133556 eq134319
  have eq134356 : False := by grind
  exact eq134356

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    grind
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq254 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq257 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq56
  have eq393 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq67
    | exact resolve eq67 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq254
  have eq404 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq393 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq393
    | (have j0 := eq393 y x
       grind)
    | exact resolve eq393 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq393
    | (have j0 := eq393 (σ y) (σ x)
       grind)
    | exact resolve eq393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq844 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq19005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19005
    | exact resolve eq19005 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19005
  have eq19024 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19013
       have r₂ := eq28
       grind)
    | exact resolve eq19013 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19013
  have eq19026 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19024
    | exact resolve eq19024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19024
  have eq19036 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19026 eq54
    | exact resolve eq54 eq19026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19026
  have eq19079 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq19036
    | exact resolve eq19036 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036
  have eq19080 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19079
  have eq19091 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq19080
       grind)
    | exact superpose eq19080 eq54
    | exact resolve eq54 eq19080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19080
  have eq19134 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19091
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19091
    | exact resolve eq19091 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19091
  have eq19135 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19134
  have eq19138 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19135 eq28
    | exact resolve eq28 eq19135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19145 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19135 eq406
    | exact resolve eq406 eq19135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq19175 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq19145
    | exact resolve eq19145 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19145
  have eq19310 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19175 eq257
    | exact resolve eq257 eq19175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19175
  have eq19568 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19135 eq19310
    | exact resolve eq19310 eq19135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19135 eq19310
  have eq19582 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19568
  have eq20164 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19582 eq102
    | exact resolve eq102 eq19582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq19582
  have eq20182 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq20164
  have eq20192 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20182
       have r₂ := eq19138
       grind)
    | exact resolve eq20182 eq19138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19138 eq20182
  have eq20362 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq20192
       grind)
    | exact superpose eq20192 eq54
    | exact resolve eq54 eq20192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20192
  have eq20405 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20362
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20362
    | exact resolve eq20362 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20362
  have eq20406 : x = (M.op x y) := by grind
  clear eq20405
  have eq20409 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20406 eq21
    | exact resolve eq21 eq20406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq20463 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20406 eq404
    | exact resolve eq404 eq20406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq20497 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq20463
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20463
    | exact resolve eq20463 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20463
  have eq20545 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq20409
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20409
    | exact resolve eq20409 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20409
  have eq20546 : x = (M.op y y) := by
    first
    | exact superpose eq20406 eq20497
    | exact resolve eq20497 eq20406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20406 eq20497
  have eq20547 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20545 eq27
    | exact resolve eq27 eq20545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20700 : x = (k y x) := by
    first
    | (have i₁ := eq257 y
       have i₂ := eq20546
       grind)
    | exact superpose eq20546 eq257
    | exact resolve eq257 eq20546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq20546
  have eq21139 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq844 x y
       have i₂ := eq20700
       grind)
    | exact superpose eq20700 eq844
    | (have j0 := eq844 x y
       grind)
    | exact resolve eq844 eq20700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq20700
  have eq21143 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq21139
  have eq21147 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21143
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21143
    | exact resolve eq21143 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21143
  have eq21160 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21147
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21147
    | exact resolve eq21147 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21147
  have eq21171 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq21160
    | exact resolve eq21160 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21160
  have eq21181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20545 eq21171
    | exact resolve eq21171 eq20545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21171
  have eq21185 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq21181
       have r₂ := eq28
       grind)
    | exact resolve eq21181 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21181
  have eq21188 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21185
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21185
    | exact resolve eq21185 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21185
  have eq21191 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20545 eq21188
    | exact resolve eq21188 eq20545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20545 eq21188
  have eq21194 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq21191
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21191
    | exact resolve eq21191 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq21191
  have eq21977 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21194 eq54
    | exact resolve eq54 eq21194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq21194
  have eq22021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20547 eq21977
    | exact resolve eq21977 eq20547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20547 eq21977
  have eq22023 : False := by grind
  exact eq22023

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
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
  have eq181 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq41
    | exact resolve eq41 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq191 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq153
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq153
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq193 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq191
  have eq247 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq253 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq247 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq247
    | exact resolve eq247 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq427 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq550 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq68
  have eq564 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq569 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq564 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq564
    | (have j0 := eq564 X0
       grind)
    | exact resolve eq564 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq3348 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq427
    | exact resolve eq427 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq4140 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq430 X0 X0 X2 X3 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq430
    | exact resolve eq430 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq5045 : (σ (k (k y y) y)) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq569 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq569
    | (have j0 := eq569 y
       grind)
    | exact resolve eq569 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq5062 : (σ (k (k y y) y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5045
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq5045
    | exact resolve eq5045 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq5045
  have eq5079 : (k (k (σ y) (σ y)) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5062
       have i₂ := eq181
       grind)
    | exact superpose eq181 eq5062
    | exact resolve eq5062 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq5062
  have eq20782 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4140 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq4140
    | exact resolve eq4140 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq4140
  have eq26300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq26300
    | exact resolve eq26300 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26300
  have eq26312 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26301
       have r₂ := eq28
       grind)
    | exact resolve eq26301 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26301
  have eq26344 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26312 eq3348
    | exact resolve eq3348 eq26312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27717 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26344 eq26312
    | exact resolve eq26312 eq26344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26312 eq26344
  have eq27757 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq27717
  have eq27786 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27757 eq56
    | exact resolve eq56 eq27757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27757
  have eq27805 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq27786
  have eq27836 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq27805
  have eq27875 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq27836
    | exact resolve eq27836 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27836
  have eq28962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27875 eq82
    | exact resolve eq82 eq27875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq27875
  have eq28975 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq28962
  have eq28977 : y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq28975
       have r₂ := eq28
       grind)
    | exact resolve eq28975 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28975
  have eq29011 : (M.op x x) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3348 x y
       have i₂ := eq28977
       grind)
    | exact superpose eq28977 eq3348
    | exact resolve eq3348 eq28977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq29880 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28977
       have i₂ := eq29011
       grind)
    | exact superpose eq29011 eq28977
    | exact resolve eq28977 eq29011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28977 eq29011
  have eq29924 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq29880
  have eq29954 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq29924
       grind)
    | exact superpose eq29924 eq56
    | exact resolve eq56 eq29924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq29924
  have eq29975 : x = (M.op y y) := by grind
  clear eq29954
  have eq29987 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq29975
       grind)
    | exact superpose eq29975 eq105
    | exact resolve eq105 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq30006 : (M.op x y) = (k x y) := by grind
  have eq30012 : y = (k y x) := by
    first
    | (have i₁ := eq253 y
       have i₂ := eq29975
       grind)
    | exact superpose eq29975 eq253
    | exact resolve eq253 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30038 : x = (M.op x y) := by
    first
    | (have i₁ := eq20782 y y
       have i₂ := eq29975
       grind)
    | exact superpose eq29975 eq20782
    | exact resolve eq20782 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20782 eq29975
  have eq30041 : x = (M.op x y) := by
    first
    | (have i₁ := eq30038
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30038
    | exact resolve eq30038 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30038
  have eq30046 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq30006
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30006
    | exact resolve eq30006 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30006
  have eq30053 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq29987
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29987
    | exact resolve eq29987 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29987
  have eq30054 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30041 eq21
    | exact resolve eq21 eq30041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq30252 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30054
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30054
    | exact resolve eq30054 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30054
  have eq30257 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30252 eq27
    | exact resolve eq27 eq30252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq30617 : x = (k x y) := by
    first
    | exact superpose eq30041 eq30046
    | exact resolve eq30046 eq30041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30046
  have eq30620 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq30617
       grind)
    | exact superpose eq30617 eq45
    | exact resolve eq45 eq30617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq30617
  have eq30646 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30252 eq30620
    | exact resolve eq30620 eq30252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30620
  have eq30657 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq30646
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30646
    | exact resolve eq30646 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30646
  have eq30666 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30252 eq30657
    | exact resolve eq30657 eq30252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30657
  have eq31869 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30252 eq30053
    | exact resolve eq30053 eq30252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30053
  have eq31886 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31869 eq5079
    | exact resolve eq5079 eq31869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5079
  have eq31909 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30257 eq31886
    | exact resolve eq31886 eq30257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31886
  have eq31919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30666 eq31909
    | exact resolve eq31909 eq30666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30666 eq31909
  have eq31929 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq31919
       have r₂ := eq28
       grind)
    | exact resolve eq31919 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31919
  have eq32138 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31929 eq253
    | exact resolve eq253 eq31929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq31929
  have eq32360 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq32138 eq31869
    | exact resolve eq31869 eq32138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31869 eq32138
  have eq32385 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq32360
  have eq32409 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq32385 eq30
    | exact resolve eq30 eq32385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32385
  have eq32630 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq32409
    | exact resolve eq32409 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq32409
  have eq32691 : x = y ∨ x = y := by
    first
    | exact superpose eq30041 eq32630
    | exact resolve eq32630 eq30041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32630
  have eq32692 : x = y := by grind
  clear eq32691
  have eq32742 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32692
       grind)
    | exact superpose eq32692 eq25
    | exact resolve eq25 eq32692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32866 : x = (k x x) := by
    first
    | (have i₁ := eq30012
       have i₂ := eq32692
       grind)
    | exact superpose eq32692 eq30012
    | exact resolve eq30012 eq32692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30012 eq32692
  have eq32979 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32742
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32742
    | exact resolve eq32742 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32742
  have eq33060 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30252 eq32979
    | exact resolve eq32979 eq30252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32979
  have eq33292 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33060 eq30257
    | exact resolve eq30257 eq33060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30257 eq33060
  have eq33871 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33292 eq193
    | exact resolve eq193 eq33292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq33292
  have eq33923 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq33871
       have r₂ := eq28
       grind)
    | exact resolve eq33871 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33871
  have eq33934 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq30041 eq33923
    | exact resolve eq33923 eq30041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30041 eq33923
  have eq33937 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq33934
       have i₂ := eq32866
       grind)
    | exact superpose eq32866 eq33934
    | exact resolve eq33934 eq32866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32866 eq33934
  have eq33938 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33937 eq15
    | exact resolve eq15 eq33937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33937
  have eq34036 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33938
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33938
    | exact resolve eq33938 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq33938
  have eq34072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30252 eq34036
    | exact resolve eq34036 eq30252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30252 eq34036
  have eq34096 : False := by grind
  exact eq34096

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq69 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 X0
       have i₂ := eq14 (τ X0) (τ X1)
       grind)
    | exact superpose eq14 eq35
    | (have j1 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq35 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq374 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq375 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq379 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq375
    | (have j0 := eq375 X0
       grind)
    | exact resolve eq375 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq555 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X0 X1
       have i₂ := eq76 X0 X0
       grind)
    | exact superpose eq76 eq82
    | exact resolve eq82 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq82
  have eq2164 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq34
    | (have j1 := eq379 X0
       grind)
    | exact resolve eq34 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq379
  have eq2192 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2164 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2164
    | (have j0 := eq2164 X0
       grind)
    | exact resolve eq2164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq2193 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2192 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192
  have eq2198 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2193 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2193
    | exact resolve eq2193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2209 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq2193 X0
       grind)
    | exact superpose eq2193 eq10
    | exact resolve eq10 eq2193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2249 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2198 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2198
    | exact resolve eq2198 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2532 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq2249 X0
       grind)
    | exact superpose eq2249 eq10
    | exact resolve eq10 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2585 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2532 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2532
    | exact resolve eq2532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532
  have eq2734 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2585 (σ X0)
       grind)
    | exact superpose eq2585 eq15
    | exact resolve eq15 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2755 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2734 X0
       have i₂ := eq2249 X0
       grind)
    | exact superpose eq2249 eq2734
    | exact resolve eq2734 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249 eq2734
  have eq3042 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2209 X0
       have i₂ := eq2585 X0
       grind)
    | exact superpose eq2585 eq2209
    | exact resolve eq2209 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209 eq2585
  have eq3274 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (τ X0)
       have i₂ := eq3042 X0
       grind)
    | exact superpose eq3042 eq25
    | exact resolve eq25 eq3042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3548 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq2755 X0
       grind)
    | exact superpose eq2755 eq25
    | exact resolve eq25 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507868 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq3042 X1
       grind)
    | exact superpose eq3042 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq3042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3042
  have eq508211 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3274 X1
       have i₂ := eq507868 X0 X1
       grind)
    | (have i₁ := eq3274 X0
       have i₂ := eq507868 (M.op X0 X0) X1
       grind)
    | exact superpose eq507868 eq3274
    | (have j1 := eq507868 X0 X1
       grind)
    | exact resolve eq3274 eq507868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274 eq507868
  have eq508426 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq508211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508211
  have eq585978 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (k X1 (σ X0))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq508426 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq508426
    | exact resolve eq508426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508426
  have eq586927 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (k (τ X1) X0) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq585978 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq585978
    | (have j0 := eq585978 X0 X1
       grind)
    | exact resolve eq585978 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq585978
  have eq590796 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq586927 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq586927
    | exact resolve eq586927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590841 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq586927 X1 X0
       grind)
    | exact superpose eq586927 eq18
    | (have j1 := eq586927 X1 X0
       grind)
    | exact resolve eq18 eq586927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq586927
  have eq592337 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq590796 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq590796
    | (have j0 := eq590796 (σ X0) (σ X1)
       grind)
    | exact resolve eq590796 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590796
  have eq592925 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq590841 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq590841
    | exact resolve eq590841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590841
  have eq593625 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq592925 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq592925
    | (have j0 := eq592925 X0 X1
       grind)
    | exact resolve eq592925 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592925
  have eq993216 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq592337 x y
       grind)
    | exact superpose eq592337 eq16
    | (have j1 := eq592337 x y
       grind)
    | exact resolve eq16 eq592337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592337
  have eq994836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq993216
       have i₂ := eq593625 x y
       grind)
    | exact superpose eq593625 eq993216
    | (have j1 := eq593625 (σ x) (σ y)
       grind)
    | (have r₁ := eq993216
       have r₂ := eq593625 x y
       grind)
    | exact resolve eq993216 eq593625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593625 eq993216
  have eq994838 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq994836
  have eq994869 : (M.op y x) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq555 x y
       have i₂ := eq994838
       grind)
    | exact superpose eq994838 eq555
    | exact resolve eq555 eq994838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996159 : y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq994838
       have i₂ := eq994869
       grind)
    | exact superpose eq994869 eq994838
    | exact resolve eq994838 eq994869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994838 eq994869
  have eq996598 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq996159
  have eq997722 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq555 (σ x) (σ y)
       have i₂ := eq996598
       grind)
    | exact superpose eq996598 eq555
    | exact resolve eq555 eq996598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq998301 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq997722
       have i₂ := eq2755 x
       grind)
    | exact superpose eq2755 eq997722
    | exact resolve eq997722 eq2755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755 eq997722
  have eq1009338 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq996598
       have i₂ := eq998301
       grind)
    | exact superpose eq998301 eq996598
    | exact resolve eq996598 eq998301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996598 eq998301
  have eq1009853 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq1009338
  have eq1010329 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1009853
       grind)
    | exact superpose eq1009853 eq10
    | exact resolve eq10 eq1009853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009853
  have eq1010812 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1010329
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1010329
    | exact resolve eq1010329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010329
  have eq1010813 : y = (M.op x x) := by grind
  clear eq1010812
  have eq1011015 : x = (M.op x y) := by
    first
    | (have i₁ := eq25 x
       have i₂ := eq1010813
       grind)
    | exact superpose eq1010813 eq25
    | exact resolve eq25 eq1010813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1011028 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3548 x
       have i₂ := eq1010813
       grind)
    | exact superpose eq1010813 eq3548
    | exact resolve eq3548 eq1010813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3548 eq1010813
  have eq1069502 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1011028
       grind)
    | exact superpose eq1011028 eq16
    | exact resolve eq16 eq1011028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011028
  have eq1070216 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1069502
       have i₂ := eq1011015
       grind)
    | exact superpose eq1011015 eq1069502
    | exact resolve eq1069502 eq1011015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011015 eq1069502
  have eq1070217 : False := by grind
  exact eq1070217

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
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
  clear eq36
  have eq47 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq89 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq228 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op (τ X0) x) ∨ x = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq11 x (τ X0)
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x (τ X0)
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq249 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq274 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq328 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq337 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq412 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X0 X0) X0 X1 X2
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49
    | (have j0 := eq49 y x X0 X1
       grind)
    | exact resolve eq49 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq49
  have eq470 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq274 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq274
    | (have j0 := eq274 X0 y
       grind)
    | exact resolve eq274 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq274
    | (have j0 := eq274 X0 (M.op x y)
       grind)
    | exact resolve eq274 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq566 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq50
    | (have j1 := eq61 X0 X0
       grind)
    | exact resolve eq50 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq577 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq572 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq580 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq584 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq577 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq577 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq577 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq577 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq593 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq584
    | (have j0 := eq584 X0 X1
       grind)
    | exact resolve eq584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq3405 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq425
    | exact resolve eq425 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq3432 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3405 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3405
    | (have j0 := eq3405 y x
       grind)
    | exact resolve eq3405 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3434 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3405
    | (have j0 := eq3405 (σ y) (σ x)
       grind)
    | exact resolve eq3405 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3405
  have eq3588 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq430 x X1 X0
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq430
    | exact resolve eq430 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq3638 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3588 sF0 sF0
       have i₂ := eq50 sF0
       grind)
    | exact superpose eq50 eq3588
    | exact resolve eq3588 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3588
  have eq3758 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq580 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq580
    | (have j0 := eq580 (τ X0)
       grind)
    | exact resolve eq580 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq580
  have eq3778 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3758 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3758
    | (have j0 := eq3758 X0
       grind)
    | exact resolve eq3758 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3758
  have eq3790 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3778 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3778
    | (have j0 := eq3778 X0
       grind)
    | exact resolve eq3778 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778
  have eq3809 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq421 (M.op y X0) X0
       have i₂ := eq52 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq52 eq421
    | exact resolve eq421 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq5347 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq7020 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq412 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq52 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq52 eq412
    | exact resolve eq412 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq13942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13942
    | exact resolve eq13942 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13942
  have eq13960 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13949
       have r₂ := eq28
       grind)
    | exact resolve eq13949 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13949
  have eq13962 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13960
    | exact resolve eq13960 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13960
  have eq13972 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13962 eq50
    | exact resolve eq50 eq13962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13962
  have eq13995 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13972
    | exact resolve eq13972 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13972
  have eq13996 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13995
  have eq14006 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq13996
       grind)
    | exact superpose eq13996 eq50
    | exact resolve eq50 eq13996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13996
  have eq14029 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14006
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14006
    | exact resolve eq14006 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14006
  have eq14030 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14029
  have eq14161 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14030 eq3434
    | exact resolve eq3434 eq14030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3434
  have eq14169 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14161
    | exact resolve eq14161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14161
  have eq14181 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14169 eq249
    | exact resolve eq249 eq14169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14462 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14030 eq14181
    | exact resolve eq14181 eq14030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14030 eq14181
  have eq14471 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14462
  have eq14910 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14471 eq100
    | exact resolve eq100 eq14471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq14471
  have eq14924 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14910
  have eq16560 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq14924
       grind)
    | exact superpose eq14924 eq50
    | exact resolve eq50 eq14924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq14924
  have eq16584 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16560
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16560
    | exact resolve eq16560 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16560
  have eq16585 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq16584
  have eq16588 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16585 eq30
    | exact resolve eq30 eq16585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16661 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16585 eq14169
    | exact resolve eq14169 eq16585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14169 eq16585
  have eq16702 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq16661
  have eq16761 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq16588
    | exact resolve eq16588 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16588
  have eq16818 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16761 eq471
    | exact resolve eq471 eq16761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq16827 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16761 eq3638
    | exact resolve eq3638 eq16761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq16832 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq16834 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16818 X0
       have i₂ := eq470 X0
       grind)
    | exact superpose eq470 eq16818
    | exact resolve eq16818 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq16818
  have eq21946 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3809 x
       have i₂ := eq16827
       grind)
    | exact superpose eq16827 eq3809
    | exact resolve eq3809 eq16827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809 eq16827
  have eq22022 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21946
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq21946
    | exact resolve eq21946 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21946
  have eq23453 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22022 eq14
    | exact resolve eq14 eq22022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22022
  have eq57023 : (τ (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y)))) = (τ (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16834 (σ (M.op (τ sF3) (τ sF3)))
       have i₂ := eq328 sF3
       grind)
    | exact superpose eq328 eq16834
    | exact resolve eq16834 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq16834
  have eq57282 : (M.op (τ (σ y)) (τ (σ y))) = (τ (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57023
       have i₂ := eq16 (M.op (τ sF3) (τ sF3))
       grind)
    | exact superpose eq16 eq57023
    | exact resolve eq57023 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57023
  have eq57296 : (M.op (τ (σ y)) (τ (σ y))) = (k (M.op (τ (σ y)) (τ (σ y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57282
       have i₂ := eq337 (M.op (τ sF3) (τ sF3)) sF1
       grind)
    | exact superpose eq337 eq57282
    | exact resolve eq57282 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq57282
  have eq57301 : (M.op (τ (σ y)) (τ (σ y))) = (k (M.op (τ (σ y)) (τ (σ y))) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq57296
    | exact resolve eq57296 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57296
  have eq57303 : (M.op y y) = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq57301
    | exact resolve eq57301 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57301
  have eq134789 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f134789_13 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
      intro X0 X1
      grind
    have f134789_14 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f134789_23 : (M.op (M.op x y) (M.op x y)) ≠ (M.op x (M.op x y)) := by grind
    have f134789_24 : x ≠ (M.op x y) := by grind
    have f134789_26 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) := by
      intro X0
      first
      | (have j0 := f134789_14 X0
         grind)
      | (have r₁ := f134789_14 X0
         have r₂ := f134789_24
         grind)
      | exact resolve f134789_14 f134789_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f134789_100 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) := by
      first
      | (have i₁ := f134789_13 x (M.op (M.op x y) (M.op x y))
         have i₂ := f134789_26 x
         grind)
      | exact superpose f134789_26 f134789_13
      | exact resolve f134789_13 f134789_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f134789_121 : False := by
      first
      | (have r₁ := f134789_100
         have r₂ := f134789_23
         grind)
      | exact resolve f134789_100 f134789_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f134789_121
  clear eq7020 eq23453
  have eq135144 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq16761 eq134789
    | exact resolve eq134789 eq16761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16761 eq134789
  have eq135212 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq135144
       have r₂ := eq16832
       grind)
    | exact resolve eq135144 eq16832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832 eq135144
  have eq135213 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135212
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq135212
    | exact resolve eq135212 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135212
  have eq135221 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57303
       have i₂ := eq135213
       grind)
    | exact superpose eq135213 eq57303
    | exact resolve eq57303 eq135213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57303 eq135213
  have eq135267 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq135221
  have eq135631 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq135267 eq593
    | (have j0 := eq593 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq593 eq135267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq135267
  have eq135636 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq135631
  have eq135637 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq135636
  have eq135663 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq135637
    | exact resolve eq135637 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135637
  have eq139153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq135663 eq16702
    | exact resolve eq16702 eq135663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16702 eq135663
  have eq139312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq139153
  have eq139324 : x = (M.op x y) := by
    first
    | (have r₁ := eq139312
       have r₂ := eq28
       grind)
    | exact resolve eq139312 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139312
  have eq140015 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq139324 eq21
    | exact resolve eq21 eq139324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140157 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq139324 eq3432
    | exact resolve eq3432 eq139324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432
  have eq140174 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq140157
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq140157
    | exact resolve eq140157 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq140157
  have eq140302 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq140015
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq140015
    | exact resolve eq140015 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140015
  have eq140303 : x = (M.op y y) := by
    first
    | exact superpose eq139324 eq140174
    | exact resolve eq140174 eq139324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140174
  have eq140304 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq140302 eq27
    | exact resolve eq27 eq140302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140703 : y = (k y x) := by
    first
    | (have i₁ := eq249 y
       have i₂ := eq140303
       grind)
    | exact superpose eq140303 eq249
    | exact resolve eq249 eq140303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq140711 : y = (M.op x x) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq140303
       grind)
    | exact superpose eq140303 eq52
    | exact resolve eq52 eq140303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq140303
  have eq141033 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq87
       have i₂ := eq140703
       grind)
    | exact superpose eq140703 eq87
    | exact resolve eq87 eq140703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq140703
  have eq141089 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq140302 eq141033
    | exact resolve eq141033 eq140302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141033
  have eq141113 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq141089
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq141089
    | exact resolve eq141089 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141089
  have eq143828 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq89 eq5347
    | (have j0 := eq5347 (M.op x y)
       grind)
    | exact resolve eq5347 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq5347
  have eq143836 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq141113 eq143828
    | exact resolve eq143828 eq141113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141113 eq143828
  have eq143871 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq143836
    | exact resolve eq143836 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143836
  have eq143905 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq143871
    | exact resolve eq143871 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143871
  have eq143937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq140304 eq143905
    | exact resolve eq143905 eq140304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143905
  have eq143955 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq143937
       have r₂ := eq28
       grind)
    | exact resolve eq143937 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143937
  have eq143971 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq143955
    | exact resolve eq143955 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq143955
  have eq150172 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op (τ X0) x) ∨ x = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq140302 eq228
    | (have j0 := eq228 X0
       grind)
    | exact resolve eq228 eq140302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq150265 : (σ (M.op x x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq150172
    | exact resolve eq150172 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq150172
  have eq150397 : (σ (M.op x x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq150265
  have eq150464 : (σ (M.op x x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq140302 eq150397
    | exact resolve eq150397 eq140302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150397
  have eq150549 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq150464
       have i₂ := eq140711
       grind)
    | exact superpose eq140711 eq150464
    | exact resolve eq150464 eq140711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150464
  have eq150619 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq150549
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq150549
    | exact resolve eq150549 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150549
  have eq150678 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq150619
       have i₂ := eq140711
       grind)
    | exact superpose eq140711 eq150619
    | exact resolve eq150619 eq140711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140711 eq150619
  have eq150931 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq150678 eq3790
    | (have j0 := eq3790 (σ (M.op x y))
       grind)
    | exact resolve eq3790 eq150678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3790
  have eq150953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq140304 eq150931
    | exact resolve eq150931 eq140304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140304 eq150931
  have eq150964 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq150953
       have r₂ := eq28
       grind)
    | exact resolve eq150953 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150953
  have eq152027 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq150964
  have eq154012 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq152027 eq150678
    | exact resolve eq150678 eq152027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150678 eq152027
  have eq154050 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq154012
  have eq154090 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq154050 eq30
    | exact resolve eq30 eq154050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq154050
  have eq154465 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq154090
    | exact resolve eq154090 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq154090
  have eq154536 : x = y ∨ x = y := by
    first
    | exact superpose eq139324 eq154465
    | exact resolve eq154465 eq139324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139324 eq154465
  have eq154537 : x = y := by grind
  clear eq154536
  have eq154593 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq154537
       grind)
    | exact superpose eq154537 eq25
    | exact resolve eq25 eq154537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq154537
  have eq154962 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq154593
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq154593
    | exact resolve eq154593 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq154593
  have eq155100 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq140302 eq154962
    | exact resolve eq154962 eq140302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154962
  have eq155228 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq155100 eq27
    | exact resolve eq27 eq155100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq155524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq155100 eq143971
    | (have r₁ := eq143971
       have r₂ := eq155100
       grind)
    | exact resolve eq143971 eq155100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143971 eq155100
  have eq155529 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq155524
  have eq155605 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq140302 eq155228
    | exact resolve eq155228 eq140302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140302 eq155228
  have eq159102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq155529 eq155605
    | exact resolve eq155605 eq155529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155529 eq155605
  have eq159103 : False := by grind
  exact eq159103
