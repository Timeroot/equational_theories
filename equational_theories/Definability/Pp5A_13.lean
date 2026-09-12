import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq75 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq75
    | (have j0 := eq75 (σ X0) (σ X1)
       grind)
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq75 y x
       grind)
    | exact superpose eq75 eq72
    | (have j1 := eq75 y x
       grind)
    | exact resolve eq72 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq119 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (k (M.op (M.op X1 X2) X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq160 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq75 sF0 sF0
       grind)
    | exact superpose eq75 eq129
    | (have j1 := eq75 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq129 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq209 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq204 eq14
    | exact resolve eq14 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq218 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq209 eq14
    | exact resolve eq14 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq236 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op X0 (M.op (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ x) X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq378 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x X0 X1 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op x X0) (M.op (M.op (M.op x x) x) X0) X2
       have i₂ := eq52 x x x X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X2 X3) X1) X0) (M.op (M.op (M.op X1 X0) X4) X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op (M.op X1 X2) X0) X3) (M.op X0 X3) X2
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 : G, y = (M.op (M.op (M.op X0 x) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq53 x X0 x
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq479 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op (M.op x x) (M.op x sF2))
       have i₂ := eq53 sF2 x x
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq585 : ∀ X0 X1 X2 X4 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X4) (M.op X1 X2)) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq56 X2 X1 (M.op (M.op X0 x) (M.op X0 X1)) X4
       have i₂ := eq53 X1 X0 x
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X0 X2) X5) (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0) X5
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) X1) X5) (M.op X0 X1)) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 X0 (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X2 X3
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq91 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op (σ X1) X2) (σ X0)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (σ X1) X2
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq14
    | (have j1 := eq91 X0 X1
       grind)
    | exact resolve eq14 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq739 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq729 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq729
    | (have j0 := eq729 X0 X1
       grind)
    | exact resolve eq729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq815 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) X1) X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op (M.op X1 X0) X4) (M.op (M.op (M.op X2 X3) X1) X0)) (M.op (M.op (M.op X1 X0) X4) (M.op (M.op (M.op X2 X3) X1) X0))) = (k (M.op (M.op (M.op X1 X0) X4) (M.op (M.op (M.op X2 X3) X1) X0)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq119 (M.op (M.op (M.op X1 X2) X0) X3) (M.op X0 X3) X2
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq119
    | (have j0 := eq119 X0 (M.op (M.op X2 X3) X1) X2
       grind)
    | exact resolve eq119 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq109 eq75
    | (have j0 := eq75 (σ y) (σ x)
       grind)
    | exact resolve eq75 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1023
    | exact resolve eq1023 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1027 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1024
       have r₂ := eq27
       grind)
    | exact resolve eq1024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1032 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1027 eq479
    | exact resolve eq479 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq1033 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1027 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1027
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1027
       grind)
    | exact resolve eq12 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1044 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1033
  have eq1045 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1032
    | exact resolve eq1032 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1051 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op (M.op x y) (M.op (M.op X1 X2) X0)) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq208
    | exact resolve eq208 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq1103 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1045 eq218
    | exact resolve eq218 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq1045
  have eq1313 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq378 (M.op x X0) (M.op (M.op (M.op x x) x) X0)
       have i₂ := eq52 x x x X0
       grind)
    | exact superpose eq52 eq378
    | exact resolve eq378 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq2456 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq397 (M.op X0 X1) (M.op (M.op (M.op X0 x) X1) x) X1
       have i₂ := eq56 X1 X0 x x
       grind)
    | exact superpose eq56 eq397
    | exact resolve eq397 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2777 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq383 X2 (M.op X1 (M.op X0 X1)) X1
       have i₂ := eq404 X1 X0
       grind)
    | exact superpose eq404 eq383
    | exact resolve eq383 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq7176 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op y X1) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq476 eq451
    | exact resolve eq451 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq476
  have eq7953 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X1 (M.op (M.op X0 X1) X3)) X3) := by
    intro X0 X1 X3
    by_contra hcon
    push Not at hcon
    have f7953_10 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
      intro X0 X1 X2
      grind
    have f7953_11 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
      intro X0 X1 X2
      grind
    have f7953_18 : (M.op (M.op X0 X1) X3) ≠ (M.op (M.op X1 (M.op (M.op X0 X1) X3)) X3) := by grind
    have f7953_49 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X1 (M.op (M.op X0 X1) X3)) X3) := by
      intro X0 X1 X3
      first
      | (have i₁ := f7953_10 X0 (M.op (M.op X1 x) (M.op X1 X0)) x
         have i₂ := f7953_11 X0 X1 x
         grind)
      | exact superpose f7953_11 f7953_10
      | exact resolve f7953_10 f7953_11
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7953_471 : (M.op (M.op X0 X1) X3) ≠ (M.op (M.op X0 X1) X3) := by
      first
      | (have i₁ := f7953_18
         have i₂ := f7953_49 X0 X1 X3
         grind)
      | exact superpose f7953_49 f7953_18
      | (have r₁ := f7953_18
         have r₂ := f7953_49 X0 X1 X3
         grind)
      | exact resolve f7953_18 f7953_49
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7953_493 : False := by grind
    exact f7953_493
  clear eq53
  have eq8156 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq657 (M.op X1 X0) X1 X0
       have i₂ := eq52 X1 X1 X0 X0
       grind)
    | exact superpose eq52 eq657
    | exact resolve eq657 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq11348 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq373 eq459
    | exact resolve eq459 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq459
  have eq11432 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq11348 x
       have i₂ := eq657 sF2 x sF3
       grind)
    | exact superpose eq657 eq11348
    | exact resolve eq11348 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq11348
  have eq12106 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (M.op (M.op X0 X0) X1) x X0
       have i₂ := eq450 X0 X0 (M.op (M.op X0 X0) X1) x X1
       grind)
    | exact superpose eq450 eq56
    | exact resolve eq56 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq450
  have eq17252 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq236 sF4 (M.op (M.op x sF2) sF4)
       have i₂ := eq587 sF2 x sF4 sF3
       grind)
    | exact superpose eq587 eq236
    | exact resolve eq236 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq587
  have eq21641 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 X1 x X0 (M.op X0 X0)
       have i₂ := eq585 (M.op X1 x) X0 X0 (M.op X1 X0)
       grind)
    | exact superpose eq585 eq636
    | exact resolve eq636 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq28381 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq129 eq731
    | (have j0 := eq731 (M.op x y) (M.op x y) x
       grind)
    | exact resolve eq731 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq731
  have eq28472 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq28381
    | (have j0 := eq28381 X0
       grind)
    | exact resolve eq28381 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28381
  have eq28512 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq28472
    | (have j0 := eq28472 X0
       grind)
    | exact resolve eq28472 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28472
  have eq37652 : ∀ X0 X1 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X0 X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq634 X1 X0 x X0 (M.op X0 X0) X3
       have i₂ := eq585 (M.op X1 x) X0 X0 (M.op X1 X0)
       grind)
    | exact superpose eq585 eq634
    | exact resolve eq634 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37970 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1 x x (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq585 (M.op (M.op (M.op X0 x) X1) x) (M.op X0 X1) (M.op X0 X1) X1
       grind)
    | exact superpose eq585 eq634
    | exact resolve eq634 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq634
  have eq252961 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1044 eq109
    | exact resolve eq109 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq252973 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq252961
  have eq253149 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq252973 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq252973
       grind)
    | exact resolve eq13 eq252973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252973
  have eq253355 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq253149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253149
  have eq257158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq253355 eq109
    | exact resolve eq109 eq253355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq253355
  have eq257189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq257158
  have eq257204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq257189
    | exact resolve eq257189 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257189
  have eq257209 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq257204
       have r₂ := eq27
       grind)
    | exact resolve eq257204 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257204
  have eq257426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq257209 eq1103
    | exact resolve eq1103 eq257209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq257209
  have eq257830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq257426
  have eq257844 : x = (M.op y x) := by
    first
    | (have r₁ := eq257830
       have r₂ := eq27
       grind)
    | exact resolve eq257830 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257830
  have eq257868 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1313 y
       have i₂ := eq257844
       grind)
    | exact superpose eq257844 eq1313
    | exact resolve eq1313 eq257844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq257875 : x ≠ x ∨ x = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq257844
       grind)
    | exact superpose eq257844 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq257844
       grind)
    | exact resolve eq12 eq257844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257900 : ∀ X0 : G, (M.op (M.op x X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq383 y x X0
       have i₂ := eq257844
       grind)
    | exact superpose eq257844 eq383
    | exact resolve eq383 eq257844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq257902 : ∀ X0 : G, x = (M.op (M.op (M.op X0 y) x) x) := by
    intro X0
    first
    | (have i₁ := eq397 y X0 x
       have i₂ := eq257844
       grind)
    | exact superpose eq257844 eq397
    | exact resolve eq397 eq257844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq257967 : x = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq2456 y x
       have i₂ := eq257844
       grind)
    | exact superpose eq257844 eq2456
    | exact resolve eq2456 eq257844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2456
  have eq257972 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq8156 x y
       have i₂ := eq257844
       grind)
    | exact superpose eq257844 eq8156
    | exact resolve eq8156 eq257844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257980 : x = (M.op x x) ∨ (k y x) = (M.op y y) := by grind
  clear eq257875
  have eq257981 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq257972
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq257972
    | exact resolve eq257972 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257972
  have eq257985 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq257868
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq257868
    | exact resolve eq257868 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq257868
  have eq258204 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq257985 eq160
    | exact resolve eq160 eq257985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq258205 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq257985 eq214
    | exact resolve eq214 eq257985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq258276 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq257985 eq12106
    | exact resolve eq12106 eq257985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257985
  have eq258413 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq258204
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq258204
    | exact resolve eq258204 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258204
  have eq269565 : ∀ X0 : G, (M.op X0 X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq37970 x X0
       have i₂ := eq257900 X0
       grind)
    | exact superpose eq257900 eq37970
    | exact resolve eq37970 eq257900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37970
  have eq269869 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq269565 (M.op x X0)
       have i₂ := eq257900 X0
       grind)
    | exact superpose eq257900 eq269565
    | exact resolve eq269565 eq257900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269896 : ∀ X0 X1 : G, (M.op x X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq269565 X0
       grind)
    | (have i₁ := eq13 X0 x
       have i₂ := eq269565 x
       grind)
    | exact superpose eq269565 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq269565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276527 : ∀ X1 : G, x ≠ x ∨ x = (M.op x x) ∨ (k (M.op (M.op (M.op x x) X1) x) x) = (M.op (M.op (M.op (M.op x x) X1) x) (M.op (M.op (M.op x x) X1) x)) := by
    intro X1
    first
    | (have i₁ := eq815 x x x y x
       have i₂ := eq257902 x
       grind)
    | exact superpose eq257902 eq815
    | (have j0 := eq815 x X1 x x x
       grind)
    | (have r₁ := eq815 x x x y x
       have r₂ := eq257902 x
       grind)
    | exact resolve eq815 eq257902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq257902
  have eq276666 : ∀ X1 : G, x = (M.op x x) ∨ (k (M.op (M.op (M.op x x) X1) x) x) = (M.op (M.op (M.op (M.op x x) X1) x) (M.op (M.op (M.op x x) X1) x)) := by
    intro X1
    first
    | (have j0 := eq276527 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276527
  have eq276684 : ∀ X1 : G, (k (M.op (M.op (M.op x x) X1) x) x) = (M.op x (M.op (M.op (M.op x x) X1) x)) ∨ x = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq276666 X1
       have i₂ := eq269565 (M.op (M.op (M.op x x) X1) x)
       grind)
    | exact superpose eq269565 eq276666
    | exact resolve eq276666 eq269565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276666
  have eq276699 : ∀ X1 : G, (k (M.op (M.op (M.op x x) X1) x) x) = (M.op x (M.op (M.op (M.op x x) X1) x)) := by
    intro X1
    first
    | (have j0 := eq276684 X1
       have j1 := eq13 (M.op (M.op (M.op x x) X1) x) x
       grind)
    | (have r₁ := eq276684 X1
       have r₂ := eq13 x x
       grind)
    | exact resolve eq276684 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276684
  have eq276704 : (M.op x (M.op x x)) = (k (M.op x x) x) := by
    first
    | (have i₁ := eq276699 x
       have i₂ := eq12106 x x
       grind)
    | exact superpose eq12106 eq276699
    | exact resolve eq276699 eq12106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12106 eq276699
  have eq276705 : x = (k (M.op x x) x) := by
    first
    | (have i₁ := eq276704
       have i₂ := eq257967
       grind)
    | exact superpose eq257967 eq276704
    | exact resolve eq276704 eq257967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257967 eq276704
  have eq351711 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq11432 eq7953
    | exact resolve eq7953 eq11432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7953 eq11432
  have eq352545 : (M.op x (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq351711
       have i₂ := eq269565 sF3
       grind)
    | exact superpose eq269565 eq351711
    | exact resolve eq351711 eq269565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351711
  have eq388943 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq257980
       have i₂ := eq258205
       grind)
    | exact superpose eq258205 eq257980
    | exact resolve eq257980 eq258205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257980
  have eq388945 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq388943
       grind)
    | exact superpose eq388943 eq72
    | exact resolve eq72 eq388943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq388943
  have eq388983 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq388945
    | exact resolve eq388945 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388945
  have eq389034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq388983 eq75
    | (have j0 := eq75 (σ y) (σ x)
       grind)
    | exact resolve eq75 eq388983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq388983
  have eq389048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq389034
    | exact resolve eq389034 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq389034
  have eq389055 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq389048
       have r₂ := eq27
       grind)
    | exact resolve eq389048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389048
  have eq389155 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq389055 eq17252
    | exact resolve eq17252 eq389055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389055
  have eq389359 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq352545 eq389155
    | exact resolve eq389155 eq352545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389155
  have eq432472 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y x) (M.op x y))) = (M.op (M.op (M.op (M.op x y) X1) (M.op X0 (M.op (M.op y x) (M.op x y)))) (M.op (M.op y x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq7176 eq37652
    | exact resolve eq37652 eq7176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7176 eq37652
  have eq434978 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op x y) X1) (M.op X0 y)) y) := by
    intro X0 X1
    first
    | exact superpose eq258276 eq432472
    | exact resolve eq432472 eq258276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258276 eq432472
  have eq435766 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op y (M.op (M.op x y) y))) y) := by
    intro X0
    first
    | (have i₁ := eq434978 (M.op x (M.op y (M.op sF0 y))) y
       have i₂ := eq2777 sF0 y x
       grind)
    | exact superpose eq2777 eq434978
    | exact resolve eq434978 eq2777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777 eq434978
  have eq436096 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op y (M.op (M.op x y) y))) y) := by
    intro X0
    first
    | (have i₁ := eq435766 X0
       have i₂ := eq258205
       grind)
    | exact superpose eq258205 eq435766
    | exact resolve eq435766 eq258205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435766
  have eq461598 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq28512 X0
       have i₂ := eq269565 sF1
       grind)
    | exact superpose eq269565 eq28512
    | (have j0 := eq28512 X0
       grind)
    | exact resolve eq28512 eq269565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28512
  have eq461691 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq461598 eq8156
    | exact resolve eq8156 eq461598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8156 eq461598
  have eq461937 : (σ (M.op x y)) = (M.op x (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | (have i₁ := eq461691
       have i₂ := eq269565 (k sF1 sF1)
       grind)
    | exact superpose eq269565 eq461691
    | exact resolve eq461691 eq269565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461691
  have eq461991 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq461937 eq257900
    | exact resolve eq257900 eq461937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257900 eq461937
  have eq462190 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq269896 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq461991
       have r₂ := eq269896 (σ (M.op x y)) x
       grind)
    | exact resolve eq461991 eq269896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269896 eq461991
  have eq462202 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    first
    | (have i₁ := eq462190
       have i₂ := eq269565 sF1
       grind)
    | exact superpose eq269565 eq462190
    | exact resolve eq462190 eq269565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462190
  have eq462204 : (σ y) = (M.op x (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq258413 eq462202
    | exact resolve eq462202 eq258413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258413
  have eq462298 : (σ (M.op x y)) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq462204 eq269869
    | exact resolve eq269869 eq462204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269869 eq462204
  have eq463023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq462298 eq389359
    | exact resolve eq389359 eq462298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389359
  have eq463311 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq463023
       have r₂ := eq27
       grind)
    | exact resolve eq463023 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463023
  have eq465307 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq276705
       have i₂ := eq463311
       grind)
    | exact superpose eq463311 eq276705
    | exact resolve eq276705 eq463311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463311
  have eq468206 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq739 x x
       have i₂ := eq465307
       grind)
    | exact superpose eq465307 eq739
    | (have j0 := eq739 x x
       grind)
    | exact resolve eq739 eq465307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465307
  have eq468211 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq468206
  have eq468212 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq468211
  have eq468220 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq468212
       have i₂ := eq269565 (σ x)
       grind)
    | exact superpose eq269565 eq468212
    | exact resolve eq468212 eq269565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468212
  have eq468242 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq468220
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq468220
    | exact resolve eq468220 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468220
  have eq470002 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq468242 eq17252
    | exact resolve eq17252 eq468242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468242
  have eq470244 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq352545 eq470002
    | exact resolve eq470002 eq352545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470002
  have eq473513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq470244 eq462298
    | exact resolve eq462298 eq470244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462298 eq470244
  have eq473763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq473513
  have eq473801 : y = (M.op x y) := by
    first
    | (have r₁ := eq473763
       have r₂ := eq27
       grind)
    | exact resolve eq473763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473763
  have eq473824 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq473801 eq20
    | exact resolve eq20 eq473801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474217 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq473801 eq257981
    | exact resolve eq257981 eq473801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257981
  have eq474272 : x = (M.op x x) := by
    first
    | (have i₁ := eq474217
       have i₂ := eq257844
       grind)
    | exact superpose eq257844 eq474217
    | exact resolve eq474217 eq257844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257844 eq474217
  have eq474370 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq473824
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq473824
    | exact resolve eq473824 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq473824
  have eq477033 : x = (k x x) := by
    first
    | (have i₁ := eq276705
       have i₂ := eq474272
       grind)
    | exact superpose eq474272 eq276705
    | exact resolve eq276705 eq474272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276705 eq474272
  have eq478913 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq739 x x
       have i₂ := eq477033
       grind)
    | exact superpose eq477033 eq739
    | (have j0 := eq739 x x
       grind)
    | exact resolve eq739 eq477033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq477033
  have eq478918 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq478913
  have eq478919 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq478918
  have eq478927 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq478919
       have i₂ := eq269565 (σ x)
       grind)
    | exact superpose eq269565 eq478919
    | exact resolve eq478919 eq269565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269565 eq478919
  have eq478949 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq478927
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq478927
    | exact resolve eq478927 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq478927
  have eq480535 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq478949 eq17252
    | exact resolve eq17252 eq478949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17252 eq478949
  have eq480809 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq352545 eq480535
    | exact resolve eq480535 eq352545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352545 eq480535
  have eq480884 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq474370 eq480809
    | exact resolve eq480809 eq474370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480809
  have eq491473 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op y (M.op (M.op X1 X2) X0)) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq473801 eq1051
    | exact resolve eq1051 eq473801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq493048 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op (M.op y (M.op x y)) (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq436096 eq491473
    | exact resolve eq491473 eq436096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436096 eq491473
  have eq496064 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op (M.op y y) (M.op X0 y))) := by
    intro X0
    first
    | exact superpose eq473801 eq493048
    | exact resolve eq493048 eq473801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493048
  have eq496655 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq496064 X0
       have i₂ := eq21641 y X0
       grind)
    | exact superpose eq21641 eq496064
    | exact resolve eq496064 eq21641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21641 eq496064
  have eq496883 : ∀ X0 : G, (M.op x y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq496655 X0
       have i₂ := eq258205
       grind)
    | exact superpose eq258205 eq496655
    | exact resolve eq496655 eq258205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496655
  have eq497003 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq473801 eq496883
    | exact resolve eq496883 eq473801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473801 eq496883
  have eq497700 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq497003 y
       grind)
    | exact superpose eq497003 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq497003 y
       grind)
    | exact resolve eq13 eq497003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497003
  have eq498914 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq497700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497700
  have eq555469 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq498914 y
       grind)
    | exact superpose eq498914 eq73
    | exact resolve eq73 eq498914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq498914
  have eq555570 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq555469
       have i₂ := eq258205
       grind)
    | exact superpose eq258205 eq555469
    | exact resolve eq555469 eq258205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258205 eq555469
  have eq555634 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq474370 eq555570
    | exact resolve eq555570 eq474370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474370 eq555570
  have eq555684 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq462202 eq555634
    | exact resolve eq555634 eq462202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462202 eq555634
  have eq555731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq480884 eq555684
    | exact resolve eq555684 eq480884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480884 eq555684
  have eq555762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq555731
    | exact resolve eq555731 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq555731
  have eq555789 : False := by grind
  exact eq555789

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
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
  have eq29 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq39 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq29 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq395 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq396 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq401 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq396 X0 X1
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq396 X0 X1
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq396 X1 X1
       have r₂ := eq96 X1 X1
       grind)
    | exact resolve eq396 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq396
  have eq584 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq401 (σ X1) (σ X0)
       grind)
    | exact superpose eq401 eq15
    | exact resolve eq15 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq401 X1 X0
       grind)
    | exact superpose eq401 eq584
    | exact resolve eq584 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq584
  have eq594 : False := by grind
  exact eq594

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq91 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq91
    | exact resolve eq91 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq91
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq176 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq167
    | (have j0 := eq167 X0 X1
       grind)
    | exact resolve eq167 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq604 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | (have j0 := eq176 (M.op X1 X1) X1
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq618 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq604 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq604
    | (have j0 := eq604 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq604 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq604
  have eq621 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq618 X0 X1
       have j1 := eq118 X1 X0
       grind)
    | (have r₁ := eq618 X0 X0
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq618 (σ (M.op X0 X0)) X0
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq618 (σ X0) (M.op X0 X0)
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq618 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq618
  have eq623 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq621
    | exact resolve eq621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq621 (σ X0) X1
       grind)
    | exact superpose eq621 eq15
    | (have j1 := eq621 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq663 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq623 (τ X1) X0
       grind)
    | exact superpose eq623 eq19
    | (have j1 := eq623 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq623
  have eq741 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq663
    | exact resolve eq663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq790 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq741
    | (have j0 := eq741 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq741 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq945 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq634 x y
       grind)
    | exact superpose eq634 eq16
    | (have j1 := eq634 x y
       grind)
    | exact resolve eq16 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq945
       have i₂ := eq790 y x
       grind)
    | exact superpose eq790 eq945
    | (have j1 := eq790 (σ x) (σ y)
       grind)
    | (have r₁ := eq945
       have r₂ := eq790 y x
       grind)
    | (have r₁ := eq945
       have r₂ := eq790 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq945
       have r₂ := eq790 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq945 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq945
  have eq961 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq960
  have eq964 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq961
       grind)
    | exact superpose eq961 eq16
    | exact resolve eq16 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq965 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq964
       have r₂ := eq102 x
       grind)
    | exact resolve eq964 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq966 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq965
       grind)
    | exact superpose eq965 eq16
    | exact resolve eq16 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq965
       grind)
    | exact superpose eq965 eq10
    | exact resolve eq10 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1012 : x = y := by
    first
    | (have i₁ := eq967
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq967
    | exact resolve eq967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq1013 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq966
       have i₂ := eq102 x
       grind)
    | exact superpose eq102 eq966
    | exact resolve eq966 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq966
  have eq1014 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1013
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq1013
    | exact resolve eq1013 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq1013
  have eq1015 : False := by grind
  exact eq1015

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pxy_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq248 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq264 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq269 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq250 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq250 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq271 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq264 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq264 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq264 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq279 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq269 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq269
    | (have j0 := eq269 X0 X1
       grind)
    | exact resolve eq269 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq280 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq281 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq271
    | (have j0 := eq271 X0 X1
       grind)
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq285 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       have j1 := eq280 X0 X1
       grind)
    | (have r₁ := eq282 X0 X1
       have r₂ := eq280 X0 X1
       grind)
    | exact resolve eq282 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq282
  have eq286 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq285
    | exact resolve eq285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq285 x y
       grind)
    | exact superpose eq285 eq16
    | exact resolve eq16 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq358 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq286 X0 (τ X1)
       grind)
    | exact superpose eq286 eq17
    | exact resolve eq17 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq286
  have eq384 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq358 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq358
    | exact resolve eq358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq396 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq384
    | exact resolve eq384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq425 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq297
       have i₂ := eq396 x y
       grind)
    | exact superpose eq396 eq297
    | exact resolve eq297 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq396
  have eq426 : False := by grind
  exact eq426

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
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
  clear eq23
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq63 (τ X0)
       grind)
    | exact superpose eq63 eq32
    | exact resolve eq32 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq68
    | exact resolve eq68 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq417 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
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
  have eq426 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq409
    | (have j0 := eq409 X0 X1
       grind)
    | exact resolve eq409 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq771 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq426 x y
       grind)
    | exact superpose eq426 eq16
    | (have j1 := eq426 x y
       grind)
    | exact resolve eq16 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq426 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq3156 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq417
    | exact resolve eq417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq3215 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3156 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3156
    | (have j0 := eq3156 X0 X1
       grind)
    | exact resolve eq3156 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq6476 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq771
       have i₂ := eq3215 y x
       grind)
    | exact superpose eq3215 eq771
    | (have j1 := eq3215 (M.op (σ x) (σ y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq771
       have r₂ := eq3215 y x
       grind)
    | (have r₁ := eq771
       have r₂ := eq3215 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq771
       have r₂ := eq3215 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq771 eq3215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq3215
  have eq6477 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq6476
  have eq6490 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq779 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq779
    | (have j0 := eq779 (τ X1) (τ X0)
       grind)
    | exact resolve eq779 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq6555 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6490 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq6490
    | (have j0 := eq6490 X0 X1
       grind)
    | exact resolve eq6490 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6490
  have eq6589 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6555 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq6555
    | (have j0 := eq6555 X0 X1
       grind)
    | exact resolve eq6555 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6555
  have eq6618 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6589 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6589
    | (have j0 := eq6589 X0 X1
       grind)
    | exact resolve eq6589 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6589
  have eq6643 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6618 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6618
    | (have j0 := eq6618 X0 X1
       grind)
    | exact resolve eq6618 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6618
  have eq6664 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6643 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6643
    | (have j0 := eq6643 X0 X1
       grind)
    | exact resolve eq6643 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6643
  have eq6684 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6664 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq6664
    | (have j0 := eq6664 X0 X1
       grind)
    | exact resolve eq6664 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq6664
  have eq6699 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6684 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq6684
    | (have j0 := eq6684 X0 X1
       grind)
    | exact resolve eq6684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6684
  have eq6713 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6699 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6699
    | (have j0 := eq6699 X0 X1
       grind)
    | exact resolve eq6699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6699
  have eq6722 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6713 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6713
    | (have j0 := eq6713 X0 X1
       grind)
    | exact resolve eq6713 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6713
  have eq14652 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6477
       grind)
    | exact superpose eq6477 eq16
    | exact resolve eq16 eq6477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6477
  have eq14653 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14652
       have r₂ := eq77 x
       grind)
    | exact resolve eq14652 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14652
  have eq14657 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14653
       grind)
    | exact superpose eq14653 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14653
       grind)
    | exact resolve eq12 eq14653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14653
  have eq14659 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq14657
  have eq14662 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq93 x (σ y)
       have i₂ := eq14659
       grind)
    | exact superpose eq14659 eq93
    | (have j0 := eq93 x (σ y)
       grind)
    | (have r₁ := eq93 x (σ y)
       have r₂ := eq14659
       grind)
    | exact resolve eq93 eq14659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14659
  have eq14672 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq14662
  have eq14678 : (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14672
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq14672
    | exact resolve eq14672 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14672
  have eq14688 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq779 x y
       have i₂ := eq14678
       grind)
    | exact superpose eq14678 eq779
    | (have j0 := eq779 x y
       grind)
    | (have r₁ := eq779 x y
       have r₂ := eq14678
       grind)
    | exact resolve eq779 eq14678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14678
  have eq14710 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq14688
  have eq14711 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq14710
  have eq14716 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq779 x y
       grind)
    | (have r₁ := eq14711
       have r₂ := eq779 x y
       grind)
    | exact resolve eq14711 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq14711
  have eq14720 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14716
       grind)
    | exact superpose eq14716 eq16
    | exact resolve eq16 eq14716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14721 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq93 x (σ y)
       have i₂ := eq14716
       grind)
    | exact superpose eq14716 eq93
    | (have j0 := eq93 x (σ y)
       grind)
    | (have r₁ := eq93 x (σ y)
       have r₂ := eq14716
       grind)
    | exact resolve eq93 eq14716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq14716
  have eq14731 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq14721
  have eq14737 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14731
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq14731
    | exact resolve eq14731 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14731
  have eq14744 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14737
       grind)
    | exact superpose eq14737 eq10
    | exact resolve eq10 eq14737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14737
  have eq14908 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14744
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14744
    | exact resolve eq14744 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14744
  have eq14910 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14908
       grind)
    | exact superpose eq14908 eq16
    | exact resolve eq16 eq14908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14908
  have eq14911 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq14910
       have r₂ := eq77 x
       grind)
    | exact resolve eq14910 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14910
  have eq14922 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq14911
       grind)
    | exact superpose eq14911 eq10
    | exact resolve eq10 eq14911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14911
  have eq15087 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq14922
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq14922
    | exact resolve eq14922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14922
  have eq15197 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq6722 y x
       have i₂ := eq15087
       grind)
    | exact superpose eq15087 eq6722
    | (have j0 := eq6722 y x
       grind)
    | (have r₁ := eq6722 y x
       have r₂ := eq15087
       grind)
    | exact resolve eq6722 eq15087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722 eq15087
  have eq15201 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq15197
  have eq15205 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14720
       have i₂ := eq15201
       grind)
    | exact superpose eq15201 eq14720
    | exact resolve eq14720 eq15201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14720 eq15201
  have eq15214 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq15205
  have eq15215 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15214
       grind)
    | exact superpose eq15214 eq16
    | exact resolve eq16 eq15214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15214
  have eq15218 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq15215
       have r₂ := eq77 x
       grind)
    | exact resolve eq15215 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15215
  have eq15219 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15218
       grind)
    | exact superpose eq15218 eq16
    | exact resolve eq16 eq15218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15220 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15218
       grind)
    | exact superpose eq15218 eq10
    | exact resolve eq10 eq15218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15218
  have eq15385 : x = y := by
    first
    | (have i₁ := eq15220
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15220
    | exact resolve eq15220 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15220
  have eq15386 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15219
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq15219
    | exact resolve eq15219 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq15219
  have eq15387 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq15386
       have i₂ := eq15385
       grind)
    | exact superpose eq15385 eq15386
    | exact resolve eq15386 eq15385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15385 eq15386
  have eq15388 : False := by grind
  exact eq15388

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq90 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq90
    | exact resolve eq90 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq90
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq101
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq101 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq118 X0 X1
       grind)
    | (have r₁ := eq134 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq134 X0 (σ (M.op X0 X0))
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq134 (M.op X0 X0) (σ X0)
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq134 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq134
  have eq163 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq141 X1 (σ X0)
       grind)
    | exact superpose eq141 eq15
    | (have j1 := eq141 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq175 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq163 (τ X1) X0
       grind)
    | exact superpose eq163 eq19
    | (have j1 := eq163 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq163
  have eq261 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq175
    | exact resolve eq175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq286 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq261
    | (have j0 := eq261 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq856 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq168 x y
       grind)
    | exact superpose eq168 eq16
    | (have j1 := eq168 x y
       grind)
    | exact resolve eq16 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq870 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq856
       have i₂ := eq286 y x
       grind)
    | exact superpose eq286 eq856
    | (have j1 := eq286 (σ x) (σ y)
       grind)
    | (have r₁ := eq856
       have r₂ := eq286 y x
       grind)
    | (have r₁ := eq856
       have r₂ := eq286 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq856
       have r₂ := eq286 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq856 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq856
  have eq871 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq870
  have eq873 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq871
       grind)
    | exact superpose eq871 eq16
    | exact resolve eq16 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq874 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq873
       have r₂ := eq101 x
       grind)
    | exact resolve eq873 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq875 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq874
       grind)
    | exact superpose eq874 eq16
    | exact resolve eq16 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq876 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq874
       grind)
    | exact superpose eq874 eq10
    | exact resolve eq10 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq917 : x = y := by
    first
    | (have i₁ := eq876
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq876
    | exact resolve eq876 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq918 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq875
       have i₂ := eq101 x
       grind)
    | exact superpose eq101 eq875
    | exact resolve eq875 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq875
  have eq919 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq918
       have i₂ := eq917
       grind)
    | exact superpose eq917 eq918
    | exact resolve eq918 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq918
  have eq920 : False := by grind
  exact eq920

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
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
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X1 (M.op X2 (M.op X0 X2)))) = X1 ∨ (k X1 (M.op X1 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X1 (M.op X2 (M.op X0 X2)))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 (M.op X1 (M.op X2 (M.op X0 X2)))
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op X2 (M.op X0 X2)))
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq216 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op X0 (M.op X1 (σ x))) X0) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq53 X2 X0 X1 x
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X3 X2)) X1)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X3 (M.op X2 (M.op X3 X2)) X0 X2
       have i₂ := eq53 (M.op X2 (M.op X3 X2)) (M.op X2 (M.op X3 X2)) X0 X1
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq689 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq775 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))) = X0 ∨ (k X0 (M.op X0 (M.op X1 (M.op X0 X1)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq792 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq506 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq506
    | exact resolve eq506 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq506
    | exact resolve eq506 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq506
    | exact resolve eq506 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq794 eq506
    | exact resolve eq506 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq829 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq795 eq506
    | exact resolve eq506 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq853 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq511
    | (have j0 := eq511 X0 (σ x) (σ y)
       grind)
    | exact resolve eq511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq938 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq816 eq14
    | exact resolve eq14 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq960 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq829 eq14
    | exact resolve eq14 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq998 : (σ y) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op (σ x) (σ y)) y)) (σ x)) := by
    first
    | (have i₁ := eq853 (M.op sF4 y)
       have i₂ := eq938 sF4
       grind)
    | exact superpose eq938 eq853
    | exact resolve eq853 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq1006 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) x) (M.op (σ y) y)) := by
    first
    | (have i₁ := eq960 (M.op sF3 y)
       have i₂ := eq938 sF3
       grind)
    | exact superpose eq938 eq960
    | exact resolve eq960 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1009 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) = X0 := by
    intro X0
    first
    | exact superpose eq960 eq506
    | exact resolve eq506 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq1111 : (M.op (σ y) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq52 eq1009
    | exact resolve eq1009 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1009
  have eq1235 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq792
    | (have j0 := eq792 (σ y) X0 (σ x)
       grind)
    | exact resolve eq792 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq45703 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X0) ∨ (k X0 (M.op X0 (M.op X1 (M.op X0 X1)))) = X0 := by
    intro X0 X1
    grind
  clear eq775
  have eq45858 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 (M.op X0 X1)))) = X0 ∨ (k X0 (M.op X0 (M.op X1 (M.op X0 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45703 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq45703
    | (have j0 := eq45703 X0 X1
       grind)
    | exact resolve eq45703 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45703
  have eq45859 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 (M.op X0 X1)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45858 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45858
  have eq46270 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 (M.op X1 X1)) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45859 X1 x
       have i₂ := eq53 X1 X0 X1 x
       grind)
    | exact superpose eq53 eq45859
    | exact resolve eq45859 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq46278 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 (M.op X1 X0)) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45859 X1 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq569 (M.op (M.op X0 (M.op X1 X0)) X1) X1 X0 X1
       grind)
    | exact superpose eq569 eq45859
    | exact resolve eq45859 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq45859
  have eq60003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq60003
    | exact resolve eq60003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60003
  have eq60018 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq60010
       have r₂ := eq28
       grind)
    | exact resolve eq60010 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60010
  have eq60020 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq60018
    | exact resolve eq60018 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60018
  have eq60032 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq60020
  have eq60209 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq60032
    | exact resolve eq60032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60032
  have eq60254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq60209 eq111
    | exact resolve eq111 eq60209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60209
  have eq60265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60254
  have eq60267 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq60265
       have r₂ := eq28
       grind)
    | exact resolve eq60265 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60265
  have eq60402 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60267
  have eq60577 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq60402
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60402
    | exact resolve eq60402 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60402
  have eq60614 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq60577
       grind)
    | exact superpose eq60577 eq70
    | exact resolve eq70 eq60577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60577
  have eq60640 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq60614
    | exact resolve eq60614 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60614
  have eq61084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60640 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq60640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq61084
    | exact resolve eq61084 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61084
  have eq61101 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq61093
       have r₂ := eq28
       grind)
    | exact resolve eq61093 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61093
  have eq61103 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq61101
    | exact resolve eq61101 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61101
  have eq61104 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq61103
  have eq61117 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq61104
  have eq61294 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq61117
    | exact resolve eq61117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61117
  have eq61458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61294 eq60640
    | exact resolve eq60640 eq61294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60640 eq61294
  have eq61466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq61458
  have eq61470 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq61466
       have r₂ := eq28
       grind)
    | exact resolve eq61466 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61466
  have eq61472 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61470 eq28
    | exact resolve eq28 eq61470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61499 : (σ y) = (M.op (M.op (M.op (M.op x y) x) (M.op (σ y) y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61470 eq998
    | exact resolve eq998 eq61470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq61549 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1006 eq61499
    | exact resolve eq61499 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq61499
  have eq61683 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq61549 eq216
    | exact resolve eq216 eq61549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq61549
  have eq61869 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1111 eq61683
    | exact resolve eq61683 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq61683
  have eq61904 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq960 eq61869
    | (have j0 := eq61869 (σ x)
       grind)
    | exact resolve eq61869 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq61869
  have eq63183 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op (σ y) (σ x))) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61904 eq46278
    | exact resolve eq46278 eq61904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46278 eq61904
  have eq63185 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1235 eq63183
    | exact resolve eq63183 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq63183
  have eq63310 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61470 eq63185
    | exact resolve eq63185 eq61470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61470 eq63185
  have eq63322 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq63310
  have eq63331 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63322 eq80
    | exact resolve eq80 eq63322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq63332 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63322 eq111
    | exact resolve eq111 eq63322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq63322
  have eq63351 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq63332
  have eq63362 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq63351
       have r₂ := eq61472
       grind)
    | exact resolve eq63351 eq61472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61472 eq63351
  have eq63363 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq63331
    | exact resolve eq63331 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq63331
  have eq63380 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq63362
  have eq63555 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq63380
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq63380
    | exact resolve eq63380 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq63380
  have eq63660 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq63363
       have i₂ := eq63555
       grind)
    | exact superpose eq63555 eq63363
    | exact resolve eq63363 eq63555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63363 eq63555
  have eq63668 : y = (M.op x y) := by grind
  clear eq63660
  have eq63710 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq63668 eq21
    | exact resolve eq21 eq63668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq63712 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y y)) X0) := by
    intro X0
    first
    | exact superpose eq63668 eq51
    | exact resolve eq51 eq63668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq63668
  have eq63892 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq63710
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq63710
    | exact resolve eq63710 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63710
  have eq63901 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq63892 eq27
    | exact resolve eq27 eq63892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq64607 : y = (k y x) := by
    first
    | (have i₁ := eq46270 x y
       have i₂ := eq63712 x
       grind)
    | exact superpose eq63712 eq46270
    | exact resolve eq46270 eq63712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46270 eq63712
  have eq65003 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq64607
       grind)
    | exact superpose eq64607 eq70
    | exact resolve eq70 eq64607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq65018 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq689 x y
       have i₂ := eq64607
       grind)
    | exact superpose eq64607 eq689
    | (have j0 := eq689 x y
       grind)
    | exact resolve eq689 eq64607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq64607
  have eq65019 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq65018
  have eq65026 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65019
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq65019
    | exact resolve eq65019 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65019
  have eq65039 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq63892 eq65003
    | exact resolve eq65003 eq63892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65003
  have eq65041 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63892 eq65026
    | exact resolve eq65026 eq63892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65026
  have eq65053 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq65039
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq65039
    | exact resolve eq65039 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65039
  have eq65054 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65041
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65041
    | exact resolve eq65041 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65041
  have eq65065 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq63892 eq65053
    | exact resolve eq65053 eq63892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65053
  have eq65066 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63901 eq65054
    | exact resolve eq65054 eq63901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65054
  have eq65072 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq65066
       have r₂ := eq28
       grind)
    | exact resolve eq65066 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65066
  have eq65078 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65072
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65072
    | exact resolve eq65072 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq65072
  have eq65084 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65078
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq65078
    | exact resolve eq65078 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq65078
  have eq65090 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63892 eq65084
    | exact resolve eq65084 eq63892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63892 eq65084
  have eq65165 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq65090
  have eq65339 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq63901 eq65165
    | exact resolve eq65165 eq63901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63901 eq65165
  have eq65398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65065 eq65339
    | exact resolve eq65339 eq65065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65065 eq65339
  have eq65425 : False := by grind
  exact eq65425

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq44
    | (have j1 := eq72 x y
       grind)
    | exact resolve eq44 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq111 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq49
    | exact resolve eq49 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq120 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq117
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq117
    | exact resolve eq117 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq117
  have eq949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq104 eq72
    | (have j0 := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq72 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq104
  have eq950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq949
    | exact resolve eq949 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq953 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq950
       have r₂ := eq27
       grind)
    | exact resolve eq950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq955 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq953
    | exact resolve eq953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq962 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq955 eq14
    | exact resolve eq14 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq967 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f967_13 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) ∨ (M.op x y) = (M.op y y) := by
      intro X0
      grind
    have f967_20 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f967_23 : (M.op x y) ≠ (M.op y y) := by grind
    have f967_24 : (σ y) ≠ (σ x) := by grind
    have f967_26 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
      intro X0
      first
      | (have j0 := f967_13 X0
         grind)
      | (have r₁ := f967_13 X0
         have r₂ := f967_23
         grind)
      | exact resolve f967_13 f967_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f967_27 : (σ y) = (σ x) := by
      first
      | (have i₁ := f967_26 x
         have i₂ := f967_20 (σ x) x (σ y)
         grind)
      | exact superpose f967_20 f967_26
      | exact resolve f967_26 f967_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f967_28 : False := by
      first
      | (have r₁ := f967_27
         have r₂ := f967_24
         grind)
      | exact resolve f967_27 f967_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f967_28
  clear eq51 eq962
  have eq974 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y (M.op x y))) X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 y
       have i₂ := eq967
       grind)
    | exact superpose eq967 eq14
    | exact resolve eq14 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq979 : (σ x) = (σ y) ∨ x = y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f979_13 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y (M.op x y))) X0) ∨ (σ x) = (σ y) := by
      intro X0
      grind
    have f979_20 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f979_23 : (σ x) ≠ (σ y) := by grind
    have f979_24 : y ≠ x := by grind
    have f979_26 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
      intro X0
      first
      | (have j0 := f979_13 X0
         grind)
      | (have r₁ := f979_13 X0
         have r₂ := f979_23
         grind)
      | exact resolve f979_13 f979_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f979_27 : y = x := by
      first
      | (have i₁ := f979_26 x
         have i₂ := f979_20 x x y
         grind)
      | exact superpose f979_20 f979_26
      | exact resolve f979_26 f979_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f979_28 : False := by
      first
      | (have r₁ := f979_27
         have r₂ := f979_24
         grind)
      | exact resolve f979_27 f979_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f979_28
  clear eq50 eq974
  have eq989 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq979 eq29
    | exact resolve eq29 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq979
  have eq1011 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq989
    | exact resolve eq989 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq989
  have eq1012 : x = y := by grind
  clear eq1011
  have eq1017 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq18
    | exact resolve eq18 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1018 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq24
    | exact resolve eq24 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1012
  have eq1041 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1018
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1018
    | exact resolve eq1018 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1018
  have eq1046 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1041 eq26
    | exact resolve eq26 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1041
  have eq1088 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1046 eq120
    | exact resolve eq120 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1046
  have eq1099 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1088
       have i₂ := eq1017
       grind)
    | exact superpose eq1017 eq1088
    | exact resolve eq1088 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq1088
  have eq1100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1099 eq15
    | exact resolve eq15 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1100
    | exact resolve eq1100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1100
  have eq1126 : False := by grind
  exact eq1126
