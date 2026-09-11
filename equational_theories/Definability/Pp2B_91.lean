import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyy_x_pxx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  clear eq44
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq10
    | exact resolve eq10 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq50
    | exact resolve eq50 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq68
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq68
    | exact resolve eq68 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq66
    | exact resolve eq66 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
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
  clear eq45
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
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
  have eq85 : (M.op x x) = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq101 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq64 sF3
       grind)
    | exact superpose eq64 eq97
    | exact resolve eq97 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq64 y
       grind)
    | exact superpose eq64 eq101
    | exact resolve eq101 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq138 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq16
    | exact resolve eq16 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq227 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq51 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq35
    | exact resolve eq35 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq308 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq297 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq297
    | exact resolve eq297 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq311 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq308 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq308
    | exact resolve eq308 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq308
  have eq420 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq429 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
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
  have eq447 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  have eq467 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq735 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq51
    | exact resolve eq51 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq840 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq311 X0
       grind)
    | exact superpose eq311 eq16
    | exact resolve eq16 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq1770 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq228 eq447
    | exact resolve eq447 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq1790 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq447 X0 X0 X0
       grind)
    | exact superpose eq447 eq447
    | exact resolve eq447 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1823 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq447 X0 X0 X0
       grind)
    | exact superpose eq447 eq14
    | exact resolve eq14 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1825 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq447 X0 X0 X0
       grind)
    | exact superpose eq447 eq51
    | exact resolve eq51 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1833 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq420 (M.op x (M.op x x))
       have i₂ := eq447 x x x
       grind)
    | exact superpose eq447 eq420
    | exact resolve eq420 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq447
  have eq1873 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq227 eq1770
    | exact resolve eq1770 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq2093 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq426 X0
       have i₂ := eq1825 X0
       grind)
    | exact superpose eq1825 eq426
    | exact resolve eq426 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq2168 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq735 eq2093
    | exact resolve eq2093 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq2093
  have eq2560 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1833 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1833
    | exact resolve eq1833 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq2605 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2560 X0 X1
       have i₂ := eq1825 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1825 eq2560
    | exact resolve eq2560 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq2621 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2605 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2605
    | exact resolve eq2605 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2605
  have eq34534 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq467 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1823 X0 X0 X1
       grind)
    | exact superpose eq1823 eq467
    | exact resolve eq467 eq1823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823
  have eq34618 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34534 X0 X1 x x x
       have i₂ := eq467 X0 X0 x x x
       grind)
    | exact superpose eq467 eq34534
    | exact resolve eq34534 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq34534
  have eq47584 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2621 eq14
    | exact resolve eq14 eq2621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621
  have eq55031 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq47584 eq1790
    | exact resolve eq1790 eq47584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790 eq47584
  have eq55689 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op (M.op X0 (M.op y X0)) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq227 eq55031
    | exact resolve eq55031 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq55031
  have eq56062 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 (M.op y X0)))) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55689 X0 X1
       have i₂ := eq1825 (M.op X0 (M.op y X0))
       grind)
    | exact superpose eq1825 eq55689
    | exact resolve eq55689 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825 eq55689
  have eq56279 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 (M.op y (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq429 eq56062
    | exact resolve eq56062 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq56062
  have eq58409 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op y (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq56279 eq1873
    | exact resolve eq1873 eq56279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873 eq56279
  have eq58455 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (M.op x y)) (M.op y (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58409 X1 (τ X0)
       have i₂ := eq840 X0
       grind)
    | exact superpose eq840 eq58409
    | exact resolve eq58409 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq87831 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq58409 X0 y
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq58409
    | exact resolve eq58409 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq87922 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq58409 eq87831
    | exact resolve eq87831 eq58409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58409 eq87831
  have eq89654 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq87922 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87922
  have eq89655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq89654
    | exact resolve eq89654 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89654
  have eq89666 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq89655
       have r₂ := eq28
       grind)
    | exact resolve eq89655 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89655
  have eq89826 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op X0 (M.op x y)) (M.op y (τ (M.op (σ x) (σ x))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq89666 eq58455
    | exact resolve eq58455 eq89666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89666
  have eq89899 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq58455 eq89826
    | exact resolve eq89826 eq58455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58455 eq89826
  have eq89976 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq89899
    | exact resolve eq89899 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq89899
  have eq89998 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq89976
    | exact resolve eq89976 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89976
  have eq89999 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq89998
  have eq90761 : (τ (σ x)) = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq89999 eq138
    | exact resolve eq138 eq89999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq89999
  have eq91027 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq90761
    | exact resolve eq90761 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq90761
  have eq91028 : x = (M.op y y) ∨ x = y := by grind
  clear eq91027
  have eq91185 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2168 y
       have i₂ := eq91028
       grind)
    | exact superpose eq91028 eq2168
    | exact resolve eq2168 eq91028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq91289 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq34618 y y
       have i₂ := eq91028
       grind)
    | exact superpose eq91028 eq34618
    | exact resolve eq34618 eq91028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34618 eq91028
  have eq91298 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq91289
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91289
    | exact resolve eq91289 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91289
  have eq91343 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91185
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq91185
    | exact resolve eq91185 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91185
  have eq91413 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91343
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq91343
    | exact resolve eq91343 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91343
  have eq91455 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq91413
    | exact resolve eq91413 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91413
  have eq91488 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq91298 eq21
    | exact resolve eq21 eq91298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91298
  have eq91784 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq91488
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq91488
    | exact resolve eq91488 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91488
  have eq92589 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq91455 eq28
    | exact resolve eq28 eq91455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91455
  have eq93677 : x = y := by
    first
    | (have r₁ := eq92589
       have r₂ := eq91784
       grind)
    | exact resolve eq92589 eq91784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91784 eq92589
  have eq93678 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq93677
       grind)
    | exact superpose eq93677 eq19
    | exact resolve eq19 eq93677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq93679 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq93677
       grind)
    | exact superpose eq93677 eq25
    | exact resolve eq25 eq93677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq93677
  have eq93979 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq93679
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq93679
    | exact resolve eq93679 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq93679
  have eq94051 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq93979 eq27
    | exact resolve eq27 eq93979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq93979
  have eq96164 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq94051 eq69
    | exact resolve eq69 eq94051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq94051
  have eq96481 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq96164
       have i₂ := eq93678
       grind)
    | exact superpose eq93678 eq96164
    | exact resolve eq96164 eq93678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93678 eq96164
  have eq96631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96481 eq15
    | exact resolve eq15 eq96481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96481
  have eq96742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq96631
    | exact resolve eq96631 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq96631
  have eq96784 : False := by grind
  exact eq96784

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pxy_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq98 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq63 sF3
       grind)
    | exact superpose eq63 eq98
    | exact resolve eq98 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq63 y
       grind)
    | exact superpose eq63 eq102
    | exact resolve eq102 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq102
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq97
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq143 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq16
    | exact resolve eq16 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq555 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1745 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq555 X0 X0 X0
       grind)
    | exact superpose eq555 eq50
    | exact resolve eq50 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1746 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq555 X0 X0 X0
       grind)
    | exact superpose eq555 eq51
    | exact resolve eq51 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq555
  have eq2021 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq1745 X0
       grind)
    | exact superpose eq1745 eq441
    | exact resolve eq441 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq2048 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1745 eq445
    | exact resolve eq445 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq2058 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq445 eq2048
    | exact resolve eq2048 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2093 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2021
    | exact resolve eq2021 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2021
  have eq2362 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1746 eq445
    | exact resolve eq445 eq1746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq2372 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq445 eq2362
    | exact resolve eq2362 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq2362
  have eq14783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq14783
    | exact resolve eq14783 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14783
  have eq14792 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq14784
       have r₂ := eq27
       grind)
    | exact resolve eq14784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14784
  have eq14795 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq14792
    | exact resolve eq14792 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14792
  have eq14798 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq14795
    | exact resolve eq14795 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14795
  have eq14801 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq14798 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq14798
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14798
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq14798
       grind)
    | exact resolve eq13 eq14798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14798
  have eq14840 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq14801
       have r₂ := eq26
       grind)
    | exact resolve eq14801 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14801
  have eq14848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq14840 eq115
    | exact resolve eq115 eq14840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq14840
  have eq14853 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14848
  have eq14855 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14853
       have r₂ := eq27
       grind)
    | exact resolve eq14853 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14853
  have eq14977 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq14855
       grind)
    | exact superpose eq14855 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq14855
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq14855
       grind)
    | exact resolve eq13 eq14855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14855
  have eq15020 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14977
       have r₂ := eq18
       grind)
    | exact resolve eq14977 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14977
  have eq15027 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq15020
       grind)
    | exact superpose eq15020 eq97
    | exact resolve eq97 eq15020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq15020
  have eq15041 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15027
    | exact resolve eq15027 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15027
  have eq15190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15041 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq15041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15190
    | exact resolve eq15190 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15190
  have eq15201 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15193
       have r₂ := eq27
       grind)
    | exact resolve eq15193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15193
  have eq15204 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15201
    | exact resolve eq15201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15201
  have eq15205 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15204
  have eq15209 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15205
    | exact resolve eq15205 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15205
  have eq15351 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15209 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15209
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15209
       grind)
    | exact resolve eq13 eq15209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15209
  have eq15390 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15351
       have r₂ := eq26
       grind)
    | exact resolve eq15351 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15351
  have eq15403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15390 eq15041
    | exact resolve eq15041 eq15390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15041 eq15390
  have eq15405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15403
  have eq15409 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15405
       have r₂ := eq27
       grind)
    | exact resolve eq15405 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15405
  have eq15565 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15409 eq2372
    | exact resolve eq2372 eq15409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372
  have eq15571 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15565
    | exact resolve eq15565 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15565
  have eq15695 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15571 eq143
    | exact resolve eq143 eq15571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq15571
  have eq15832 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2093 y
       have i₂ := eq15695
       grind)
    | exact superpose eq15695 eq2093
    | exact resolve eq2093 eq15695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15695
  have eq16437 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15409 eq15832
    | exact resolve eq15832 eq15409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15409 eq15832
  have eq16471 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by grind
  clear eq16437
  have eq16480 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq16471
    | exact resolve eq16471 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16471
  have eq16482 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16480
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16480
    | exact resolve eq16480 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16480
  have eq16483 : x = (M.op x y) := by grind
  clear eq16482
  have eq16485 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16483 eq20
    | exact resolve eq20 eq16483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16562 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq16483 eq2058
    | exact resolve eq2058 eq16483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq16580 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16562
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16562
    | exact resolve eq16562 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16562
  have eq16628 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16485
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16485
    | exact resolve eq16485 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16485
  have eq16629 : x = (M.op y y) := by
    first
    | exact superpose eq16483 eq16580
    | exact resolve eq16580 eq16483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16483 eq16580
  have eq16646 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16628 eq26
    | exact resolve eq26 eq16628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq16780 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq16629
       grind)
    | exact superpose eq16629 eq104
    | exact resolve eq104 eq16629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq16629
  have eq16896 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16780
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16780
    | exact resolve eq16780 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16780
  have eq16912 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16628 eq16896
    | exact resolve eq16896 eq16628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16628 eq16896
  have eq17009 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16912 eq2093
    | exact resolve eq2093 eq16912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093 eq16912
  have eq17063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16646 eq17009
    | exact resolve eq17009 eq16646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16646 eq17009
  have eq17087 : False := by grind
  exact eq17087

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pxy_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq11 eq13
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
  clear eq45
  have eq176 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq580 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (k X0 X1) (M.op X2 X2))) = X2 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
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
  have eq595 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq639 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq589
       grind)
    | exact superpose eq589 eq41
    | exact resolve eq41 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq640 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq639
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq639
    | exact resolve eq639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq642 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq640
    | exact resolve eq640 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq672 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq178 X0 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq28
    | exact resolve eq28 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq13
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq674 X0 X1
       have j1 := eq676 X0 X1
       grind)
    | (have r₁ := eq674 X0 X1
       have r₂ := eq676 X0 X1
       grind)
    | exact resolve eq674 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq676
  have eq759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq642 eq595
    | exact resolve eq595 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq642
  have eq766 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq759
       have r₂ := eq27
       grind)
    | exact resolve eq759 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq772 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq766 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq774 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq766 eq13
    | exact resolve eq13 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq766 eq672
    | exact resolve eq672 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq766
  have eq782 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq777
    | exact resolve eq777 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq785 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq772
       have r₂ := eq774
       grind)
    | exact resolve eq772 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772 eq774
  have eq792 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq782 eq16
    | exact resolve eq16 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq798 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq785 eq98
    | exact resolve eq98 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq785
  have eq804 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq798
    | exact resolve eq798 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq798
  have eq1006 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq178 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq177 X0 x x X3
       grind)
    | exact superpose eq177 eq178
    | exact resolve eq178 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq178
  have eq17904 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq176 eq682
    | exact resolve eq682 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq17920 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (σ x) (M.op X0 X0)) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq792 eq682
    | exact resolve eq682 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq17946 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq17920 X0
       have i₂ := eq1006 X0 sF2
       grind)
    | exact superpose eq1006 eq17920
    | exact resolve eq17920 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17920
  have eq17959 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17904 X0
       have i₂ := eq1006 X0 sF4
       grind)
    | exact superpose eq1006 eq17904
    | exact resolve eq17904 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq17904
  have eq18223 : y ≠ (k x x) ∨ y = (M.op x x) := by grind
  clear eq17946
  have eq18265 : y = (M.op x x) := by
    first
    | (have r₁ := eq18223
       have r₂ := eq804
       grind)
    | exact resolve eq18223 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq18223
  have eq18341 : y = (k x x) := by
    first
    | (have i₁ := eq18265
       have i₂ := eq17959 x
       grind)
    | exact superpose eq17959 eq18265
    | exact resolve eq18265 eq17959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18265
  have eq18372 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq18341
       grind)
    | exact superpose eq18341 eq40
    | exact resolve eq40 eq18341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18374 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq583 x X0 X1
       have i₂ := eq18341
       grind)
    | exact superpose eq18341 eq583
    | (have j0 := eq583 x X1 x
       grind)
    | exact resolve eq583 eq18341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq18376 : ∀ X0 : G, (M.op x (M.op y (M.op X0 X0))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq580 x x X0
       have i₂ := eq18341
       grind)
    | exact superpose eq18341 eq580
    | (have j0 := eq580 x x x
       grind)
    | exact resolve eq580 eq18341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq18377 : ∀ X0 : G, (M.op x (M.op y (k X0 X0))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18376 X0
       have i₂ := eq17959 X0
       grind)
    | exact superpose eq17959 eq18376
    | exact resolve eq18376 eq17959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18376
  have eq18379 : ∀ X0 X1 : G, x = (k x x) ∨ x = (M.op X0 (M.op (M.op X1 X0) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18374 X0 X1
       have i₂ := eq17959 x
       grind)
    | exact superpose eq17959 eq18374
    | (have j0 := eq18374 X0 X1
       grind)
    | exact resolve eq18374 eq17959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18374
  have eq18381 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq18372
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18372
    | exact resolve eq18372 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18372
  have eq18383 : ∀ X0 : G, x = (k x x) ∨ (M.op x (M.op y (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq18377 X0
       have i₂ := eq17959 x
       grind)
    | exact superpose eq17959 eq18377
    | (have j0 := eq18377 X0
       grind)
    | exact resolve eq18377 eq17959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18377
  have eq18385 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 X0) y)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq18379 X0 X1
       have i₂ := eq18341
       grind)
    | exact superpose eq18341 eq18379
    | (have j0 := eq18379 X0 X1
       grind)
    | exact resolve eq18379 eq18341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18379
  have eq18387 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq18381
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18381
    | exact resolve eq18381 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18381
  have eq18389 : ∀ X0 : G, (M.op x (M.op y (k X0 X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18383 X0
       have i₂ := eq18341
       grind)
    | exact superpose eq18341 eq18383
    | (have j0 := eq18383 X0
       grind)
    | exact resolve eq18383 eq18341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18383
  have eq18855 : x = (M.op (σ y) (M.op (M.op (σ x) (σ y)) y)) ∨ x = y := by
    first
    | exact superpose eq26 eq18385
    | (have j0 := eq18385 (σ y) (σ x)
       grind)
    | exact resolve eq18385 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19221 : x = (M.op (M.op (M.op (σ x) (σ y)) y) (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18855 eq18385
    | exact resolve eq18385 eq18855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18385 eq18855
  have eq19222 : x = (M.op (M.op (M.op (σ x) (σ y)) y) (M.op x y)) ∨ x = y := by grind
  clear eq19221
  have eq19223 : x = (M.op (M.op (M.op (σ x) (σ y)) y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq19222
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19222
    | exact resolve eq19222 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19222
  have eq19351 : (k x x) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq19223 eq682
    | exact resolve eq682 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19223
  have eq19387 : y = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq19351
       have i₂ := eq18341
       grind)
    | exact superpose eq18341 eq19351
    | exact resolve eq19351 eq18341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18341 eq19351
  have eq19429 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq19387 eq682
    | exact resolve eq682 eq19387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19387
  have eq19465 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq19429
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19429
    | exact resolve eq19429 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19429
  have eq19519 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq19465
       grind)
    | exact superpose eq19465 eq41
    | exact resolve eq41 eq19465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq19465
  have eq19528 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq19519
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19519
    | exact resolve eq19519 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19519
  have eq19536 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq19528
    | exact resolve eq19528 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19528
  have eq20564 : (σ x) = (M.op x (M.op y (σ y))) ∨ x = y := by
    first
    | exact superpose eq18387 eq18389
    | exact resolve eq18389 eq18387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18389
  have eq20708 : (k (σ x) (σ x)) = (M.op (M.op y (σ y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20564 eq682
    | exact resolve eq682 eq20564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20564
  have eq20738 : (σ y) = (M.op (M.op y (σ y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq18387 eq20708
    | exact resolve eq20708 eq18387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20708
  have eq20778 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20738 eq682
    | exact resolve eq682 eq20738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq20738
  have eq20808 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq20778
    | exact resolve eq20778 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20778
  have eq20825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq19536 eq20808
    | exact resolve eq20808 eq19536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19536 eq20808
  have eq20837 : x = y := by
    first
    | (have r₁ := eq20825
       have r₂ := eq27
       grind)
    | exact resolve eq20825 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20825
  have eq20844 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20837
       grind)
    | exact superpose eq20837 eq18
    | exact resolve eq18 eq20837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20845 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq20837
       grind)
    | exact superpose eq20837 eq24
    | exact resolve eq24 eq20837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq20837
  have eq20995 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20845
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20845
    | exact resolve eq20845 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20845
  have eq20996 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq20844
       have i₂ := eq17959 x
       grind)
    | exact superpose eq17959 eq20844
    | exact resolve eq20844 eq17959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20844
  have eq21033 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20995 eq26
    | exact resolve eq26 eq20995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq21213 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21033
       have i₂ := eq17959 sF2
       grind)
    | exact superpose eq17959 eq21033
    | exact resolve eq21033 eq17959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17959 eq21033
  have eq21250 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18387 eq21213
    | exact resolve eq21213 eq18387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21213
  have eq21272 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20995 eq21250
    | exact resolve eq21250 eq20995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21250
  have eq21284 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq21272 eq27
    | exact resolve eq27 eq21272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21272
  have eq21560 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq20996
       grind)
    | exact superpose eq20996 eq40
    | exact resolve eq40 eq20996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq20996
  have eq21574 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21560
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21560
    | exact resolve eq21560 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21560
  have eq21577 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18387 eq21574
    | exact resolve eq21574 eq18387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18387 eq21574
  have eq21580 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20995 eq21577
    | exact resolve eq21577 eq20995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20995 eq21577
  have eq21818 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21580 eq20
    | exact resolve eq20 eq21580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21580
  have eq21840 : False := by grind
  exact eq21840

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxx_y_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = X3 ∨ (M.op X0 X3) = (k X0 X3) ∨ (M.op X0 X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X2
       have i₂ := eq14 X0 X3
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X3
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq12
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
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
  have eq99 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq12
    | (have j0 := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq89 X0
       grind)
    | exact resolve eq12 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq99 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq141 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq25 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq24 X0 x x X3
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq24 X1 x x X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq24 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq156 X0 X1 X2 X3
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq156
    | exact resolve eq156 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153 (M.op X0 X1) x
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq153
    | exact resolve eq153 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq155 X0 X0 X0
       grind)
    | exact superpose eq155 eq9
    | exact resolve eq9 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq153 (M.op x (M.op x x)) x
       have i₂ := eq155 x x x
       grind)
    | exact superpose eq155 eq153
    | exact resolve eq153 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq155
  have eq601 : ∀ X0 X1 X2 X3 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X2 (M.op (M.op X3 X2) X0)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq70 X0 X2 X3 (τ X1)
       grind)
    | exact superpose eq70 eq19
    | (have j1 := eq70 X0 X2 X3 (τ X1)
       grind)
    | exact resolve eq19 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1067 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq512 (M.op X0 X1) X1 X0
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq512
    | exact resolve eq512 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X2
       have i₂ := eq512 X2 X0 X1
       grind)
    | exact superpose eq512 eq89
    | exact resolve eq89 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1105 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X2
       have i₂ := eq512 X2 X0 X1
       grind)
    | exact superpose eq512 eq101
    | exact resolve eq101 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1107 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq524 X2 X3
       have i₂ := eq512 X2 X0 X1
       grind)
    | exact superpose eq512 eq524
    | exact resolve eq524 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq1126 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq512 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq512 eq9
    | exact resolve eq9 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1231 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1102 (M.op X2 (M.op X0 X0)) (M.op (M.op x x) (M.op X2 X2)) X1
       have i₂ := eq24 X2 x x X0
       grind)
    | exact superpose eq24 eq1102
    | exact resolve eq1102 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1256 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1102 x x X1
       have i₂ := eq70 X1 x x X0
       grind)
    | (have i₁ := eq1102 X0 X1 x
       have i₂ := eq70 X0 X1 x (M.op X0 (M.op (M.op X1 X0) x))
       grind)
    | exact superpose eq70 eq1102
    | (have j1 := eq70 X1 X1 x X0
       grind)
    | exact resolve eq1102 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1270 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1256 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1531 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq94 X0 (M.op X1 X0) X2 X3
       have i₂ := eq512 X0 X0 X1
       grind)
    | exact superpose eq512 eq94
    | exact resolve eq94 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1546 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq94 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq94 eq94
    | exact resolve eq94 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1591 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1531 X0 X1 x x
       have i₂ := eq94 X0 X0 x x
       grind)
    | exact superpose eq94 eq1531
    | exact resolve eq1531 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1531
  have eq1792 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1105 x x X1
       have i₂ := eq70 X1 x x X0
       grind)
    | (have i₁ := eq1105 X0 X1 x
       have i₂ := eq70 X0 X1 x (M.op X0 (M.op (M.op X1 X0) x))
       grind)
    | exact superpose eq70 eq1105
    | (have j1 := eq70 X1 X1 x X0
       grind)
    | exact resolve eq1105 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1809 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1792 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1792 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1792 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq2022 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1107 (M.op X3 (M.op X0 X0)) (M.op (M.op x x) (M.op X3 X3)) X2 X1
       have i₂ := eq24 X3 x x X0
       grind)
    | exact superpose eq24 eq1107
    | exact resolve eq1107 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2876 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op (M.op (M.op X1 X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1231 X0 (M.op (M.op X1 X0) (M.op X0 X0)) x
       have i₂ := eq1107 X0 X1 (M.op X0 X0) x
       grind)
    | exact superpose eq1107 eq1231
    | exact resolve eq1231 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq2949 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2876 X0 X1
       have i₂ := eq1591 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact superpose eq1591 eq2876
    | exact resolve eq2876 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2876
  have eq2977 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2949 X0 X1
       have i₂ := eq25 X0 X0
       grind)
    | exact superpose eq25 eq2949
    | exact resolve eq2949 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2949
  have eq3579 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op X0 X1) (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq166 (M.op (M.op x x) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0))) x x
       have i₂ := eq141 X0 X1 x x X4
       grind)
    | exact superpose eq141 eq166
    | exact resolve eq166 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq3606 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq166 (M.op X1 (M.op X2 X3)) X0 X3 X2
       have i₂ := eq512 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq512 eq166
    | exact resolve eq166 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq512
  have eq3763 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3606 X0 X1 X2 X3
       have i₂ := eq1067 X0 (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq1067 eq3606
    | exact resolve eq3606 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067 eq3606
  have eq3784 : ∀ X0 X1 X4 X5 X6 : G, (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) = (M.op X1 (M.op (M.op X4 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq3579 X0 X1 X4 X5 X6
       have i₂ := eq1546 (M.op X4 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq1546 eq3579
    | exact resolve eq3579 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3854 : ∀ X0 X1 X5 X6 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (M.op X5 (M.op (M.op X6 X5) (M.op X0 X1))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq3784 X0 X1 x X5 X6
       have i₂ := eq183 X1 X0 x
       grind)
    | exact superpose eq183 eq3784
    | exact resolve eq3784 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq3784
  have eq4282 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2977 (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) X0
       have i₂ := eq1231 X2 X0 X1
       grind)
    | exact superpose eq1231 eq2977
    | exact resolve eq2977 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq2977
  have eq4445 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op (M.op X2 X0) (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4282 X0 X1 X2
       have i₂ := eq1546 (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op X1 (M.op X2 X2)) (M.op X2 X0)
       grind)
    | exact superpose eq1546 eq4282
    | exact resolve eq4282 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4282
  have eq4460 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op (M.op X2 X0) (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4445 X0 X1 X2
       have i₂ := eq3854 (M.op X1 (M.op X2 X2)) (M.op X2 X0) (M.op X2 X0) (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq3854 eq4445
    | exact resolve eq4445 eq3854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq4466 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4460 X0 X1 X2
       have i₂ := eq3763 (M.op X2 X0) X1 X2 X2
       grind)
    | exact superpose eq3763 eq4460
    | exact resolve eq4460 eq3763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3763 eq4460
  have eq4470 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op X0 (M.op (M.op X2 X0) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4466 X0 X1 X2
       have i₂ := eq1546 (M.op X2 X0) X2 X0
       grind)
    | exact superpose eq1546 eq4466
    | exact resolve eq4466 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546 eq4466
  have eq4473 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4470 X0 X1 X2
       have i₂ := eq3854 X2 X0 X0 X2
       grind)
    | exact superpose eq3854 eq4470
    | exact resolve eq4470 eq3854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470
  have eq4474 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)))) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4473 X0 X1 X2
       have i₂ := eq25 (M.op X1 (M.op X2 X2)) (M.op X2 X0)
       grind)
    | exact superpose eq25 eq4473
    | exact resolve eq4473 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4473
  have eq4475 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 (M.op X0 (M.op X2 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq4474 X0 x X2
       have i₂ := eq2022 X2 X2 X0 x
       grind)
    | exact superpose eq2022 eq4474
    | exact resolve eq4474 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022 eq4474
  have eq5698 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op (M.op x x) (M.op x x)) x
       have i₂ := eq24 x x x (M.op x x)
       grind)
    | exact superpose eq24 eq90
    | exact resolve eq90 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq90
  have eq5701 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5698 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq5698
    | (have j0 := eq5698 X0
       grind)
    | exact resolve eq5698 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5698
  have eq5732 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq5701 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq5701
    | (have j0 := eq5701 X0
       grind)
    | exact resolve eq5701 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5701
  have eq5760 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5732 X0
       have j1 := eq1270 X0 X0
       grind)
    | (have r₁ := eq5732 X0
       have r₂ := eq1270 X0 X0
       grind)
    | exact resolve eq5732 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5732
  have eq5805 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5760 (σ X0)
       grind)
    | exact superpose eq5760 eq15
    | exact resolve eq15 eq5760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5816 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5805 X0
       have i₂ := eq5760 X0
       grind)
    | exact superpose eq5760 eq5805
    | exact resolve eq5805 eq5760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5760 eq5805
  have eq6410 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq5816 X0
       grind)
    | exact superpose eq5816 eq9
    | exact resolve eq9 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6440 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1591 (σ X0) (σ X0)
       have i₂ := eq5816 X0
       grind)
    | exact superpose eq5816 eq1591
    | exact resolve eq1591 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591
  have eq11305 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (M.op (σ (σ (M.op X0 X0))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6410 (σ X0) X1
       have i₂ := eq5816 X0
       grind)
    | exact superpose eq5816 eq6410
    | exact resolve eq6410 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6410
  have eq15251 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq1809 X1 (σ X0)
       grind)
    | exact superpose eq1809 eq31
    | (have j1 := eq1809 X1 (σ X0)
       grind)
    | exact resolve eq31 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1809
  have eq15314 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15251 X0 X1
       have i₂ := eq5816 X0
       grind)
    | exact superpose eq5816 eq15251
    | (have j0 := eq15251 X0 X1
       grind)
    | exact resolve eq15251 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15251
  have eq15379 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15314 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq15314
    | (have j0 := eq15314 X0 X1
       grind)
    | exact resolve eq15314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15314
  have eq17291 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) X3)) = X0 ∨ (k (σ X3) (σ X0)) = (σ (M.op X3 X0)) ∨ (M.op X3 X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq601 X0 (σ X0) X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq601
    | exact resolve eq601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq17695 : ∀ X0 X1 X2 X3 : G, (σ (k X3 X0)) = (σ (M.op X3 X0)) ∨ (M.op X1 (M.op (M.op X2 X1) X3)) = X0 ∨ (M.op X3 X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17291 X0 X1 X2 X3
       have i₂ := eq15 X3 X0
       grind)
    | exact superpose eq15 eq17291
    | (have j0 := eq17291 X0 X1 X2 X3
       grind)
    | exact resolve eq17291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17291
  have eq166068 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4475 X3 X2
       have i₂ := eq3854 X2 X3 X0 X1
       grind)
    | exact superpose eq3854 eq4475
    | exact resolve eq4475 eq3854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854 eq4475
  have eq194117 : ∀ X0 X1 : G, (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ (M.op X0 X0)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11305 (σ X0) X1
       have i₂ := eq5816 X0
       grind)
    | exact superpose eq5816 eq11305
    | exact resolve eq11305 eq5816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11305
  have eq444767 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1105 x x X1
       have i₂ := eq17695 X0 x x X1
       grind)
    | (have i₁ := eq1105 X0 X1 x
       have i₂ := eq17695 (M.op X0 (M.op (M.op X1 X0) x)) X1 x x
       grind)
    | exact superpose eq17695 eq1105
    | (have j1 := eq17695 X0 X1 x X1
       grind)
    | exact resolve eq1105 eq17695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq17695
  have eq445549 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq444767 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq444767 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq444767 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444767
  have eq1420558 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq15379 X0 (σ X1)
       grind)
    | exact superpose eq15379 eq15
    | (have j1 := eq15379 X0 (σ X1)
       grind)
    | exact resolve eq15 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15379
  have eq1420765 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1420558 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1420558
    | (have j0 := eq1420558 X0 X1
       grind)
    | exact resolve eq1420558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420558
  have eq2588935 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1420765 x y
       grind)
    | exact superpose eq1420765 eq16
    | (have j1 := eq1420765 x y
       grind)
    | exact resolve eq16 eq1420765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420765
  have eq2590708 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq445549 y x
       grind)
    | (have r₁ := eq2588935
       have r₂ := eq445549 y x
       grind)
    | exact resolve eq2588935 eq445549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445549 eq2588935
  have eq2598375 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1270 y x
       have i₂ := eq2590708
       grind)
    | exact superpose eq2590708 eq1270
    | (have j0 := eq1270 y x
       grind)
    | exact resolve eq1270 eq2590708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270 eq2590708
  have eq2603774 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) (M.op x x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq166068 X0 X1 x y
       have i₂ := eq2598375
       grind)
    | exact superpose eq2598375 eq166068
    | exact resolve eq166068 eq2598375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598375
  have eq2603808 : (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2603774 x x
       have i₂ := eq1126 x x x x
       grind)
    | exact superpose eq1126 eq2603774
    | exact resolve eq2603774 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq2603774
  have eq2613850 : ∀ X0 : G, y = (M.op (σ (σ (σ X0))) (M.op (σ (σ (σ (M.op X0 X0)))) (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq194117 X0 y
       have i₂ := eq2603808
       grind)
    | exact superpose eq2603808 eq194117
    | exact resolve eq194117 eq2603808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603808
  have eq2614729 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2613850 x
       have i₂ := eq194117 x x
       grind)
    | exact superpose eq194117 eq2613850
    | exact resolve eq2613850 eq194117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194117 eq2613850
  have eq2620242 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq166068 X0 X1 x y
       have i₂ := eq2614729
       grind)
    | exact superpose eq2614729 eq166068
    | exact resolve eq166068 eq2614729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166068
  have eq2620272 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2620242 x x
       have i₂ := eq1102 x x x
       grind)
    | exact superpose eq1102 eq2620242
    | exact resolve eq2620242 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq2620242
  have eq2625613 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq6440 y
       have i₂ := eq2620272
       grind)
    | exact superpose eq2620272 eq6440
    | exact resolve eq6440 eq2620272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6440 eq2620272
  have eq2759680 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq2625613
       grind)
    | exact superpose eq2625613 eq16
    | exact resolve eq16 eq2625613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625613
  have eq2768115 : (σ x) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq2759680
       have i₂ := eq2614729
       grind)
    | exact superpose eq2614729 eq2759680
    | exact resolve eq2759680 eq2614729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614729 eq2759680
  have eq2768122 : (σ x) ≠ (σ x) ∨ x = y := by grind
  clear eq2768115
  have eq2768123 : x = y := by grind
  clear eq2768122
  have eq2769554 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2768123
       grind)
    | exact superpose eq2768123 eq16
    | exact resolve eq16 eq2768123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768123
  have eq2769560 : False := by grind
  exact eq2769560

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  clear eq18
  have eq30 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq55 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq55
    | exact resolve eq55 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq62 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq55 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq55 eq65
    | exact resolve eq65 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq68
    | exact resolve eq68 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq76 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X0) X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq56
    | exact resolve eq56 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq69
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq103 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq103
    | exact resolve eq103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq103 (τ X0)
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq103
    | exact resolve eq103 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq114 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq113
    | exact resolve eq113 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq112
    | exact resolve eq112 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq112
  have eq136 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq55 (τ X0) (τ X0)
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq55
    | exact resolve eq55 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq58 (τ X0)
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq58
    | exact resolve eq58 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq136 X0
       have i₂ := eq114 (M.op X0 X0)
       grind)
    | exact superpose eq114 eq136
    | exact resolve eq136 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq136
  have eq147 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq144 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq144
    | exact resolve eq144 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq157 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X0 X0))
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq63 X1 X1
       grind)
    | exact superpose eq63 eq76
    | exact resolve eq76 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq345 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | (have j0 := eq14 X2 (M.op X0 X1)
       grind)
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq140 X0
       have i₂ := eq147 X0
       grind)
    | exact superpose eq147 eq140
    | exact resolve eq140 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq147
  have eq832 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X0 (M.op X0 X0) X2 X1
       have i₂ := eq158 X0 X0
       grind)
    | exact superpose eq158 eq60
    | exact resolve eq60 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 (M.op X1 X2) (M.op X0 (M.op X1 X2)) X1 X2
       have i₂ := eq60 X0 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq969 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1
       have i₂ := eq832 X1 X2 X0
       grind)
    | exact superpose eq832 eq58
    | exact resolve eq58 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq970 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X2 (M.op (M.op X0 X2) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq158 X1 X3
       have i₂ := eq832 X1 X2 X0
       grind)
    | exact superpose eq832 eq158
    | exact resolve eq158 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq975 : ∀ X0 X1 X2 : G, (τ X1) = (M.op (τ X1) (τ (M.op X2 (M.op (M.op X0 X2) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq417 X1
       have i₂ := eq832 X1 X2 X0
       grind)
    | exact superpose eq832 eq417
    | exact resolve eq417 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : ∀ X0 X2 X3 : G, (M.op X3 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq969 (M.op x (M.op X2 X2)) X3 (M.op X2 (M.op X0 X0))
       have i₂ := eq157 x X2 X0
       grind)
    | exact superpose eq157 eq969
    | exact resolve eq969 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq1354 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X1)) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq970 X0 (M.op X0 X1) X1 X2
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq970
    | exact resolve eq970 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq970
  have eq2426 : ∀ X0 X1 X2 : G, (M.op X0 (τ (M.op X1 (M.op (M.op X2 X1) (σ X0))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq975 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq975
    | exact resolve eq975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq2600 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X3)) = (M.op (τ (M.op X2 (M.op (M.op X0 X2) (σ X1)))) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq832 X3 (τ (M.op X2 (M.op (M.op X0 X2) (σ X1)))) X1
       have i₂ := eq2426 X1 X2 X0
       grind)
    | exact superpose eq2426 eq832
    | exact resolve eq832 eq2426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq2607 : ∀ X0 X1 X2 X3 : G, (τ (M.op X2 (M.op (M.op X0 X2) (σ X1)))) = (M.op (τ (M.op X2 (M.op (M.op X0 X2) (σ X1)))) (M.op (M.op X3 (M.op X1 X1)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1105 X1 X3 (τ (M.op X2 (M.op (M.op X0 X2) (σ X1))))
       have i₂ := eq2426 X1 X2 X0
       grind)
    | exact superpose eq2426 eq1105
    | exact resolve eq1105 eq2426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq2426
  have eq2624 : ∀ X0 X1 X2 : G, (τ (M.op X2 (M.op (M.op X0 X2) (σ X1)))) = (M.op (τ (M.op X2 (M.op (M.op X0 X2) (σ X1)))) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2607 X0 X1 X2 x
       have i₂ := eq76 x X1
       grind)
    | exact superpose eq76 eq2607
    | exact resolve eq2607 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq2607
  have eq2636 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (τ (M.op X2 (M.op (M.op X0 X2) (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2624 X0 X1 X2
       have i₂ := eq2600 X0 X1 X2 X1
       grind)
    | exact superpose eq2600 eq2624
    | exact resolve eq2624 eq2600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600 eq2624
  have eq12974 : ∀ X0 X1 X2 : G, (τ X2) = (M.op (τ X2) (τ (τ (M.op X0 (M.op (M.op X1 X0) (σ X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq417 X2
       have i₂ := eq2636 X1 X2 X0
       grind)
    | exact superpose eq2636 eq417
    | exact resolve eq417 eq2636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq2636
  have eq72621 : ∀ X0 X1 X2 : G, (M.op X0 (τ (τ (M.op X1 (M.op (M.op X2 X1) (σ (σ X0))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12974 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12974
    | exact resolve eq12974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12974
  have eq204812 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) X0) (M.op X2 (M.op (M.op X1 X2) X0))) ∨ (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1354 X0 X1 X1
       have i₂ := eq345 X0 X1 X2
       grind)
    | exact superpose eq345 eq1354
    | (have j1 := eq345 X1 X2 X0
       grind)
    | exact resolve eq1354 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq1354
  have eq205549 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 (M.op X2 (M.op (M.op X1 X2) X0))) ∨ (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204812 X0 X1 X2
       have i₂ := eq835 X2 (M.op X1 X2) X0
       grind)
    | exact superpose eq835 eq204812
    | (have j0 := eq204812 X0 X1 X2
       grind)
    | exact resolve eq204812 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq204812
  have eq205860 : ∀ X0 X1 X2 : G, (M.op X1 X2) = X0 ∨ (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq205549 X0 X1 X2
       have i₂ := eq969 X1 X0 X2
       grind)
    | exact superpose eq969 eq205549
    | (have j0 := eq205549 X0 X1 X2
       grind)
    | exact resolve eq205549 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq205549
  have eq205861 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq205860 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205860
  have eq206255 : ∀ X1 X3 : G, (M.op X1 X3) = (k X3 X1) ∨ X1 = X3 := by
    intro X1 X3
    first
    | (have i₁ := eq205861 x x (τ (τ (M.op X1 (M.op (M.op x X1) (σ (σ x))))))
       have i₂ := eq72621 x X1 x
       grind)
    | exact superpose eq72621 eq205861
    | (have j0 := eq205861 (k X3 X1) X1 X3
       grind)
    | exact resolve eq205861 eq72621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72621 eq205861
  have eq206279 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq206255 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq206255
    | (have j0 := eq206255 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq206255 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206297 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq206255 (τ X0) X1
       grind)
    | exact superpose eq206255 eq19
    | (have j1 := eq206255 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq206255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq206255
  have eq206819 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq206297 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq206297
    | exact resolve eq206297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206297
  have eq207113 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq206819 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq206819
    | (have j0 := eq206819 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq206819 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206819
  have eq213638 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206279 y x
       grind)
    | exact superpose eq206279 eq16
    | (have j1 := eq206279 x y
       grind)
    | exact resolve eq16 eq206279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206279
  have eq213922 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq213638
       have i₂ := eq207113 x y
       grind)
    | exact superpose eq207113 eq213638
    | (have j1 := eq207113 (σ x) (σ y)
       grind)
    | (have r₁ := eq213638
       have r₂ := eq207113 x y
       grind)
    | (have r₁ := eq213638
       have r₂ := eq207113 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq213638
       have r₂ := eq207113 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq213638 eq207113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207113 eq213638
  have eq213923 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq213922
  have eq213929 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq213923
       grind)
    | exact superpose eq213923 eq10
    | exact resolve eq10 eq213923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213923
  have eq214120 : x = y ∨ x = y := by
    first
    | (have i₁ := eq213929
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq213929
    | exact resolve eq213929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213929
  have eq214121 : x = y := by grind
  clear eq214120
  have eq214143 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214121
       grind)
    | exact superpose eq214121 eq16
    | exact resolve eq16 eq214121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214121
  have eq214144 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq214143
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq214143
    | (have r₁ := eq214143
       have r₂ := eq115 x
       grind)
    | exact resolve eq214143 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq214143
  have eq214145 : False := by grind
  exact eq214145

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq83
    | (have j0 := eq83 (σ X0) (σ X1)
       grind)
    | exact resolve eq83 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq83 y x
       grind)
    | exact superpose eq83 eq75
    | (have j1 := eq83 y x
       grind)
    | exact resolve eq75 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq83 y y
       grind)
    | exact superpose eq83 eq76
    | (have j1 := eq83 y y
       grind)
    | exact resolve eq76 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq83 sF3 sF3
       grind)
    | exact superpose eq83 eq88
    | (have j1 := eq83 (σ y) (σ y)
       grind)
    | exact resolve eq88 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq82
    | exact resolve eq82 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq83
    | (have j0 := eq83 (σ y) (σ x)
       grind)
    | exact resolve eq83 eq115
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
  have eq124 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq121
    | exact resolve eq121 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
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
  have eq138 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq64
    | exact resolve eq64 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq143 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq27
    | exact resolve eq27 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq189 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq139 eq16
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq220 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq128 eq51
    | exact resolve eq51 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq229 eq14
    | exact resolve eq14 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op y (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq239 eq50
    | exact resolve eq50 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq332 : (σ x) = (M.op (σ y) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq309 eq229
    | exact resolve eq229 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq338 : (σ x) = (M.op (σ y) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by grind
  clear eq332
  have eq349 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq68
    | (have r₁ := eq68
       have r₂ := eq128
       grind)
    | exact resolve eq68 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq350 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq349
  have eq353 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq350 eq115
    | exact resolve eq115 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq350 eq82
    | exact resolve eq82 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq350
  have eq356 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq353
  have eq359 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq354
    | exact resolve eq354 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq364 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq356 eq29
    | exact resolve eq29 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq356 eq115
    | exact resolve eq115 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq373 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq356 eq142
    | (have r₁ := eq142
       have r₂ := eq356
       grind)
    | exact resolve eq142 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq356
  have eq384 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq373
  have eq385 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq384
  have eq386 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq372
  have eq394 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq364
    | exact resolve eq364 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq412 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 (M.op X1 X0) X0
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq394 eq29
    | exact resolve eq29 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq394
  have eq466 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq430
    | exact resolve eq430 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq489 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq359
       grind)
    | exact superpose eq359 eq124
    | exact resolve eq124 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq359
  have eq492 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq489
  have eq501 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq52
  have eq557 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq548
    | exact resolve eq548 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq558 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq547
    | exact resolve eq547 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq559 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq546 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq546
    | exact resolve eq546 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq546
  have eq642 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ (k X0 X1)) (M.op X2 X2))) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq14
    | (have j1 := eq95 X0 X1
       grind)
    | exact resolve eq14 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq691 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq386 eq385
    | exact resolve eq385 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq386
  have eq694 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq691
  have eq697 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq694
       have r₂ := eq143
       grind)
    | exact resolve eq694 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq701 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq697 eq26
    | exact resolve eq26 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq697 eq36
    | exact resolve eq36 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq708 : (k y y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq697 eq88
    | exact resolve eq88 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : (k y (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq697 eq93
    | exact resolve eq93 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq712 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq697 eq167
    | exact resolve eq167 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq718 : (σ x) = (M.op (σ (M.op x y)) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq697 eq338
    | exact resolve eq338 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq697 eq492
    | exact resolve eq492 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq721 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq720
  have eq723 : (σ x) = (M.op (σ (M.op x y)) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by grind
  clear eq718
  have eq733 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq721
       have r₂ := eq143
       grind)
    | exact resolve eq721 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq735 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq189 eq712
    | exact resolve eq712 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq736 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq189 eq709
    | exact resolve eq709 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq737 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq189 eq708
    | exact resolve eq708 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq708
  have eq741 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq703
    | exact resolve eq703 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq703
  have eq792 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq733
  have eq900 : (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq735 eq83
    | (have j0 := eq83 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq83 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq220 eq900
    | exact resolve eq900 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq904 : (M.op x y) = (M.op y (M.op x y)) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq220 eq901
    | exact resolve eq901 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq906 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq904
       have r₂ := eq13 (M.op x y) y
       grind)
    | exact resolve eq904 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq923 : (k y y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq737 eq736
    | exact resolve eq736 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq924 : (k y y) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq737 eq735
    | exact resolve eq735 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq737
  have eq927 : (k y y) = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq924
  have eq928 : (k y y) = (k y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq923
  have eq1054 : (k y y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq466 eq906
    | exact resolve eq906 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq1056 : (k y y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1054
  have eq1057 : (k y y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1056
       have r₂ := eq792
       grind)
    | exact resolve eq1056 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq1056
  have eq1071 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq220 eq412
    | exact resolve eq412 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096 : (k y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq927 eq906
    | exact resolve eq906 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq927
  have eq1099 : (k y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1096
  have eq1404 : (M.op y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1057
       have i₂ := eq1099
       grind)
    | exact superpose eq1099 eq1057
    | exact resolve eq1057 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1407 : (M.op y y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1404
  have eq1569 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq419 (M.op X0 X0) (M.op X1 (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq419
    | exact resolve eq419 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1734 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq501 X0 X0 X0
       grind)
    | exact superpose eq501 eq14
    | exact resolve eq14 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1735 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq501 X0 X0 X0
       grind)
    | exact superpose eq501 eq50
    | exact resolve eq50 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1742 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq229 (M.op X0 (M.op X0 X0))
       have i₂ := eq501 X0 X0 X0
       grind)
    | exact superpose eq501 eq229
    | exact resolve eq229 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq2459 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq741 eq38
    | exact resolve eq38 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq2497 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq2459
    | (have j0 := eq2459 X0
       grind)
    | exact resolve eq2459 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq2515 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2497 X0
       have i₂ := eq38 X0 y
       grind)
    | exact superpose eq38 eq2497
    | exact resolve eq2497 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2497
  have eq2522 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2515 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2515
    | (have j0 := eq2515 X0
       grind)
    | exact resolve eq2515 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515
  have eq4721 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq928 eq652
    | (have j0 := eq652 (M.op x y) y
       grind)
    | exact resolve eq652 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq928
  have eq4808 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4721
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq4721
    | exact resolve eq4721 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4721
  have eq4857 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4808
    | exact resolve eq4808 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4808
  have eq4898 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4857
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4857
    | exact resolve eq4857 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4857
  have eq4911 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4898
    | exact resolve eq4898 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4898
  have eq6687 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)))) = (M.op (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq557 (M.op X1 (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq557
    | exact resolve eq557 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6715 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6687 X0 X1
       have i₂ := eq542 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq542 eq6687
    | exact resolve eq6687 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6687
  have eq6762 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X1
       have i₂ := eq557 X0 X1
       grind)
    | exact superpose eq557 eq558
    | exact resolve eq558 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq6768 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq6762 x (M.op (M.op x x) (M.op X0 X0))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq6762
    | exact resolve eq6762 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6852 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6762 (M.op x sF4) (M.op X0 X0)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq6762
    | exact resolve eq6762 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7592 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq559 X0 X1 X2 X3
       have i₂ := eq557 X0 X1
       grind)
    | exact superpose eq557 eq559
    | exact resolve eq559 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq7593 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6762 eq7592
    | exact resolve eq7592 eq6762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7592
  have eq7768 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7593 X1 (M.op X0 X1) X1 X0
       have i₂ := eq557 X0 X1
       grind)
    | exact superpose eq557 eq7593
    | exact resolve eq7593 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq7769 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7593 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq501 x X1 X0
       grind)
    | exact superpose eq501 eq7593
    | exact resolve eq7593 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq7782 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7593 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq7593
    | exact resolve eq7593 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7783 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 X1)) = (M.op y (M.op (M.op x y) (M.op (M.op X4 (M.op X3 X2)) (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7593 (M.op X4 (M.op X3 X2)) (M.op X1 (M.op X0 X1)) X2 X3
       have i₂ := eq418 X1 X0 (M.op X3 X2) X4
       grind)
    | exact superpose eq418 eq7593
    | exact resolve eq7593 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq7784 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op (M.op x y) (M.op (M.op X4 (M.op X3 X2)) (M.op X0 X1)))) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7593 (M.op X4 (M.op X3 X2)) (M.op X0 X1) X2 X3
       have i₂ := eq7593 X0 X1 (M.op X3 X2) X4
       grind)
    | exact superpose eq7593 eq7593
    | exact resolve eq7593 eq7593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7593
  have eq7866 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X1)))) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq6762 eq7768
    | exact resolve eq7768 eq6762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7768
  have eq7882 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq419 eq7866
    | exact resolve eq7866 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq7866
  have eq8341 : ∀ X0 : G, (M.op (σ y) (M.op (k (σ y) (σ (M.op x y))) (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq77 eq642
    | (have j0 := eq642 y (M.op x y) x
       grind)
    | exact resolve eq642 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq642
  have eq8418 : ∀ X0 : G, (M.op (σ y) (M.op (k (σ y) (σ (M.op x y))) (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8341 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8341
    | (have j0 := eq8341 X0
       grind)
    | exact resolve eq8341 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8341
  have eq8485 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ y) (M.op (k (σ y) (σ (M.op x y))) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8418 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8418
    | (have j0 := eq8418 X0
       grind)
    | exact resolve eq8418 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8418
  have eq8537 : ∀ X0 : G, (M.op (σ y) (M.op (k (σ y) (σ (M.op x y))) (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq8485
    | (have j0 := eq8485 X0
       grind)
    | exact resolve eq8485 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8485
  have eq9062 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2522 eq4911
    | exact resolve eq4911 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522 eq4911
  have eq9064 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9062
  have eq14713 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq412 X0
       have i₂ := eq1742 X0
       grind)
    | exact superpose eq1742 eq412
    | exact resolve eq412 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq1742
  have eq14926 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq14713 eq528
    | exact resolve eq528 eq14713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14713
  have eq15001 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14926 x x
       have i₂ := eq542 sF3 (M.op x x)
       grind)
    | exact superpose eq542 eq14926
    | exact resolve eq14926 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14926
  have eq15004 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15001
    | exact resolve eq15001 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15001
  have eq15007 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq697 eq15004
    | exact resolve eq15004 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq15012 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15004 eq50
    | exact resolve eq50 eq15004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15004
  have eq15101 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq15007
  have eq15229 : (σ (M.op x y)) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15101 eq50
    | exact resolve eq50 eq15101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq15101
  have eq15548 : (σ y) = (M.op y (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq15012
    | exact resolve eq15012 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15012
  have eq15586 : (σ y) = (M.op y (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq15548
  have eq15724 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op y y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1407 eq1071
    | exact resolve eq1071 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq1407
  have eq16959 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15586 eq723
    | exact resolve eq723 eq15586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq16961 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15586 eq338
    | exact resolve eq338 eq15586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq15586
  have eq16999 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16961
  have eq17001 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16959
  have eq21571 : ∀ X0 X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op y (M.op y y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1735 eq528
    | exact resolve eq528 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq21618 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq21571 x x x
       have i₂ := eq528 y y x x x
       grind)
    | exact superpose eq528 eq21571
    | exact resolve eq21571 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21571
  have eq26726 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq128 eq6768
    | exact resolve eq6768 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq6768
  have eq49177 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq528 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1734 X0 X0 X1
       grind)
    | exact superpose eq1734 eq528
    | exact resolve eq528 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq49253 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq49177 X0 X1 x x x
       have i₂ := eq528 X0 X0 x x x
       grind)
    | exact superpose eq528 eq49177
    | exact resolve eq49177 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq49177
  have eq83640 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15724 eq7769
    | exact resolve eq7769 eq15724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7769 eq15724
  have eq83724 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq220 eq83640
    | exact resolve eq83640 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq83640
  have eq86345 : ∀ X0 : G, (M.op (M.op (k (σ y) (σ (M.op x y))) (M.op X0 X0)) X0) ≠ X0 ∨ (k X0 X0) = (M.op (M.op (k (σ y) (σ (M.op x y))) (M.op X0 X0)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq8537 eq416
    | exact resolve eq416 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq8537
  have eq86411 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = (M.op (M.op (k (σ y) (σ (M.op x y))) (M.op X0 X0)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq86345 X0
       have i₂ := eq542 X0 (k sF3 sF1)
       grind)
    | exact superpose eq542 eq86345
    | (have j0 := eq86345 X0
       grind)
    | exact resolve eq86345 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86345
  have eq86434 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq86411 X0
       have i₂ := eq542 X0 (k sF3 sF1)
       grind)
    | exact superpose eq542 eq86411
    | (have j0 := eq86411 X0
       grind)
    | exact resolve eq86411 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq86411
  have eq86443 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq86434 X0
       have j1 := eq83 X0 X0
       grind)
    | (have r₁ := eq86434 X0
       have r₂ := eq83 X0 X0
       grind)
    | exact resolve eq86434 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq86434
  have eq105088 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq6762 eq6715
    | exact resolve eq6715 eq6762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6715 eq6762
  have eq105089 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq105088 X0 x
       have i₂ := eq1569 X0 x
       grind)
    | exact superpose eq1569 eq105088
    | exact resolve eq105088 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq105088
  have eq113726 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq701 eq7782
    | exact resolve eq7782 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq7782
  have eq114834 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6852 eq113726
    | exact resolve eq113726 eq6852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6852 eq113726
  have eq717037 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X2 X0)) (M.op y (M.op (M.op x y) (σ y)))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq26726 eq7783
    | exact resolve eq7783 eq26726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7783 eq26726
  have eq717538 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ y)))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7784 eq717037
    | exact resolve eq717037 eq7784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7784 eq717037
  have eq717635 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105089 eq717538
    | exact resolve eq717538 eq105089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105089 eq717538
  have eq717662 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq717635
    | (have j0 := eq717635 X0
       grind)
    | exact resolve eq717635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717635
  have eq718437 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq717662 eq7882
    | exact resolve eq7882 eq717662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7882 eq717662
  have eq1045232 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15229 eq718437
    | exact resolve eq718437 eq15229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15229 eq718437
  have eq1045505 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1045232
  have eq1045714 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1045505 eq114834
    | exact resolve eq114834 eq1045505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114834 eq1045505
  have eq1046242 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1045714
  have eq1046868 : (σ y) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1046242 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1046242
       grind)
    | exact resolve eq12 eq1046242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046242
  have eq1047205 : (σ y) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1046868
       have r₂ := eq9064
       grind)
    | exact resolve eq1046868 eq9064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9064 eq1046868
  have eq1408063 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17001 eq1047205
    | exact resolve eq1047205 eq17001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17001 eq1047205
  have eq1408068 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1408063
  have eq1408075 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1408068
       have r₂ := eq143
       grind)
    | exact resolve eq1408068 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq1408068
  have eq5511685 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16999 eq116
    | exact resolve eq116 eq16999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq16999
  have eq5512266 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5511685
       have r₂ := eq1408075
       grind)
    | exact resolve eq5511685 eq1408075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408075 eq5511685
  have eq5512281 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq5512266
    | exact resolve eq5512266 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5512266
  have eq5512301 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1099
       have i₂ := eq5512281
       grind)
    | exact superpose eq5512281 eq1099
    | exact resolve eq1099 eq5512281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099 eq5512281
  have eq5512559 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5512301
  have eq5513457 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5512559 eq83724
    | exact resolve eq83724 eq5512559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83724 eq5512559
  have eq5514260 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5513457
  have eq5514557 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5514260
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5514260
    | exact resolve eq5514260 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5514260
  have eq5514558 : x = (M.op x y) := by grind
  clear eq5514557
  have eq5514822 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq5514558 eq20
    | exact resolve eq20 eq5514558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq5515245 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq5514558 eq21618
    | exact resolve eq21618 eq5514558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21618
  have eq5515416 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5515245
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5515245
    | exact resolve eq5515245 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5515245
  have eq5515622 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5514822
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5514822
    | exact resolve eq5514822 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5514822
  have eq5515653 : x = (M.op y y) := by
    first
    | exact superpose eq5514558 eq5515416
    | exact resolve eq5515416 eq5514558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5515416
  have eq5515745 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5515622 eq26
    | exact resolve eq26 eq5515622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq5518021 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq5515653
       grind)
    | exact superpose eq5515653 eq104
    | exact resolve eq104 eq5515653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq5518538 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq5515653
       grind)
    | exact superpose eq5515653 eq13
    | exact resolve eq13 eq5515653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5515653
  have eq5519646 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5518021
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5518021
    | exact resolve eq5518021 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5518021
  have eq5520034 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5515622 eq5519646
    | exact resolve eq5519646 eq5515622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5519646
  have eq5538190 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq5520034 eq88
    | exact resolve eq88 eq5520034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq5520034
  have eq5538583 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq5538190
    | exact resolve eq5538190 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5538190
  have eq5538679 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq5514558 eq5538583
    | exact resolve eq5538583 eq5514558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5514558 eq5538583
  have eq5538719 : x = (k y y) := by
    first
    | (have r₁ := eq5538679
       have r₂ := eq5518538
       grind)
    | exact resolve eq5538679 eq5518538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5518538 eq5538679
  have eq5538758 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq5538719
       grind)
    | exact superpose eq5538719 eq76
    | exact resolve eq76 eq5538719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq5538719
  have eq5539257 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq5538758
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5538758
    | exact resolve eq5538758 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5538758
  have eq5539494 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq5515622 eq5539257
    | exact resolve eq5539257 eq5515622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5515622 eq5539257
  have eq5540594 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5539494 eq86443
    | exact resolve eq86443 eq5539494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86443 eq5539494
  have eq5540710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5515745 eq5540594
    | exact resolve eq5540594 eq5515745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5540594
  have eq5540836 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq5540710
       have r₂ := eq27
       grind)
    | exact resolve eq5540710 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5540710
  have eq5542044 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5540836 eq49253
    | exact resolve eq49253 eq5540836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49253 eq5540836
  have eq5542245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5515745 eq5542044
    | exact resolve eq5542044 eq5515745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5515745 eq5542044
  have eq5542870 : False := by grind
  exact eq5542870

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxx_pyy_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op (M.op X2 X1) (M.op X0 X0))) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq81
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq109 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
    | (have r₁ := eq111 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq112 (σ X0)
       grind)
    | exact superpose eq112 eq10
    | exact resolve eq10 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq43
    | exact resolve eq43 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
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
  have eq118 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq117
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq117
    | exact resolve eq117 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq115
    | exact resolve eq115 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq114
    | exact resolve eq114 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq252 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq112 (τ X0)
       grind)
    | exact superpose eq112 eq34
    | exact resolve eq34 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq370 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq359 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq359
    | exact resolve eq359 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq373 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq370 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq370
    | exact resolve eq370 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq370
  have eq576 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0) (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq53
    | exact resolve eq53 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq576 X0
       have i₂ := eq121 (M.op X0 X0)
       grind)
    | exact superpose eq121 eq576
    | exact resolve eq576 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq576
  have eq603 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq602 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq602
    | exact resolve eq602 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq633 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X1) X1 X2 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq680 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq675
    | exact resolve eq675 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq681 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq674 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq674
    | exact resolve eq674 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq836 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq373 X0
       grind)
    | exact superpose eq373 eq16
    | exact resolve eq16 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq919 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq53 (M.op X2 X1) (M.op X0 X0)
       grind)
    | exact superpose eq53 eq65
    | (have j0 := eq65 X0 X1 X2
       grind)
    | (have r₁ := eq65 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq65 (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq65 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq992 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq836 X0
       grind)
    | exact superpose eq836 eq50
    | exact resolve eq50 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq1014 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op X1 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq919 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq2027 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq277 eq633
    | exact resolve eq633 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq2074 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq633 X0 X0 X0
       grind)
    | exact superpose eq633 eq50
    | exact resolve eq50 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2075 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq633 X0 X0 X0
       grind)
    | exact superpose eq633 eq51
    | exact resolve eq51 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2087 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f2087_12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
      intro X0 X1
      grind
    have f2087_13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X2))) = X2 := by
      intro X0 X1 X2
      grind
    have f2087_22 : X0 ≠ (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) := by grind
    have f2087_89 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f2087_12 (M.op x (M.op x x)) X1
         have i₂ := f2087_13 x x x
         grind)
      | exact superpose f2087_13 f2087_12
      | exact resolve f2087_12 f2087_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2087_146 : X0 ≠ X0 := by
      first
      | (have i₁ := f2087_22
         have i₂ := f2087_89 X0 X1
         grind)
      | exact superpose f2087_89 f2087_22
      | (have r₁ := f2087_22
         have r₂ := f2087_89 X0 X1
         grind)
      | exact resolve f2087_22 f2087_89
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2087_150 : False := by grind
    exact f2087_150
  clear eq669
  have eq2253 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq587 X0
       have i₂ := eq2074 X0
       grind)
    | exact superpose eq2074 eq587
    | exact resolve eq587 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2329 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2253
    | exact resolve eq2253 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2372 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq2329 X0
       grind)
    | exact superpose eq2329 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq2329 X0
       grind)
    | exact resolve eq13 eq2329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329
  have eq2392 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2372 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372
  have eq2441 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2392 (M.op x (M.op x x))
       have i₂ := eq633 x x x
       grind)
    | exact superpose eq633 eq2392
    | exact resolve eq2392 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq2392
  have eq2613 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq587 X0
       have i₂ := eq2075 X0
       grind)
    | exact superpose eq2075 eq587
    | exact resolve eq587 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq3088 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq26 eq2087
    | (have j0 := eq2087 (σ y) (σ x)
       grind)
    | exact resolve eq2087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq3154 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq3088
       have i₂ := eq2074 sF3
       grind)
    | exact superpose eq2074 eq3088
    | exact resolve eq3088 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3088
  have eq3440 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq992 eq2253
    | exact resolve eq2253 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992 eq2253
  have eq6628 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq681 X0 X1 X2 X3
       have i₂ := eq680 X0 X1
       grind)
    | exact superpose eq680 eq681
    | exact resolve eq681 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq681
  have eq6830 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6628 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq6628
    | exact resolve eq6628 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6628
  have eq7081 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq664 (M.op X0 X0) X1 X2
       have i₂ := eq1014 X0 X0
       grind)
    | exact superpose eq1014 eq664
    | exact resolve eq664 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq1014
  have eq7141 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op X0 (M.op X0 X0)) X0)) (k (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7081 X1 X1 X2
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq7081
    | exact resolve eq7081 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7081
  have eq7233 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7141 X0 X1 X2
       have i₂ := eq2441 X0
       grind)
    | exact superpose eq2441 eq7141
    | exact resolve eq7141 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441 eq7141
  have eq7389 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7233 X1 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq587 X0
       grind)
    | exact superpose eq587 eq7233
    | exact resolve eq7233 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7233
  have eq40550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq40550
    | exact resolve eq40550 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40550
  have eq40562 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq40551
       have r₂ := eq27
       grind)
    | exact resolve eq40551 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40551
  have eq40566 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq40562
    | exact resolve eq40562 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40562
  have eq40570 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq40566 eq109
    | (have r₁ := eq109
       have r₂ := eq40566
       grind)
    | exact resolve eq109 eq40566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq40683 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq40566 eq7389
    | exact resolve eq7389 eq40566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40566
  have eq40693 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq40570
  have eq40694 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq40693
  have eq40747 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq40683 eq2613
    | exact resolve eq2613 eq40683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613 eq40683
  have eq41648 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq40694 eq89
    | exact resolve eq89 eq40694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq40694
  have eq41661 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq41648
  have eq42179 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq41661 eq7389
    | exact resolve eq7389 eq41661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46417 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq42179 eq41661
    | exact resolve eq41661 eq42179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41661 eq42179
  have eq46463 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq46417
  have eq46544 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq46463 eq3440
    | exact resolve eq3440 eq46463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3440 eq46463
  have eq46626 : (τ (σ y)) = (M.op (τ (σ y)) x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq46544
    | exact resolve eq46544 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq46544
  have eq46664 : y = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq29 eq46626
    | exact resolve eq46626 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq46626
  have eq46665 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq46664
  have eq47682 : (M.op (σ y) (σ (M.op x y))) = (M.op y (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq46665 eq2074
    | exact resolve eq2074 eq46665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074
  have eq47707 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq46665 eq53
    | exact resolve eq53 eq46665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53078 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq47682 eq3154
    | exact resolve eq3154 eq47682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154 eq47682
  have eq54116 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq47707 eq53078
    | exact resolve eq53078 eq47707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47707 eq53078
  have eq54171 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq54116
  have eq54784 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq54171 eq2027
    | exact resolve eq2027 eq54171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027 eq54171
  have eq73204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq40747 eq54784
    | exact resolve eq54784 eq40747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40747 eq54784
  have eq73276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq73204
  have eq73299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq73276
    | exact resolve eq73276 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73276
  have eq73308 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq73299
       have r₂ := eq27
       grind)
    | exact resolve eq73299 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73299
  have eq73323 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq73308 eq53
    | exact resolve eq53 eq73308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq73308
  have eq73410 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq73323
    | exact resolve eq73323 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73323
  have eq73446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq73410 eq46665
    | exact resolve eq46665 eq73410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46665 eq73410
  have eq73628 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq73446
  have eq73691 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq73628
       have r₂ := eq27
       grind)
    | exact resolve eq73628 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73628
  have eq73735 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq120
       have i₂ := eq73691
       grind)
    | exact superpose eq73691 eq120
    | exact resolve eq120 eq73691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq73746 : x = (M.op y (M.op (M.op x y) (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq73691
       grind)
    | exact superpose eq73691 eq50
    | exact resolve eq50 eq73691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq73981 : x = (M.op y (M.op y (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq252 eq73746
    | exact resolve eq73746 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq73746
  have eq73990 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq73735
    | exact resolve eq73735 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73735
  have eq78783 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0)))) = (M.op x X0) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq6830 X0 x x X1
       have i₂ := eq73691
       grind)
    | exact superpose eq73691 eq6830
    | exact resolve eq6830 eq73691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6830 eq73691
  have eq79413 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq78783 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq78783
    | exact resolve eq78783 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78783
  have eq79731 : y = (M.op y (M.op y (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq587 y
       have i₂ := eq79413 y
       grind)
    | exact superpose eq79413 eq587
    | exact resolve eq587 eq79413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq79413
  have eq80185 : y = (M.op y (M.op y (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq79731
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79731
    | exact resolve eq79731 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79731
  have eq86547 : x = y ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq80185 eq73981
    | exact resolve eq73981 eq80185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73981 eq80185
  have eq86631 : y = (M.op y x) ∨ x = y := by grind
  clear eq86547
  have eq86765 : (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq7389 y x
       have i₂ := eq86631
       grind)
    | exact superpose eq86631 eq7389
    | exact resolve eq7389 eq86631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7389
  have eq87693 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq86631
       have i₂ := eq86765
       grind)
    | exact superpose eq86765 eq86631
    | exact resolve eq86631 eq86765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86631 eq86765
  have eq87760 : y = (M.op x x) ∨ x = y := by grind
  clear eq87693
  have eq87796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq603 x
       have i₂ := eq87760
       grind)
    | exact superpose eq87760 eq603
    | exact resolve eq603 eq87760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq87760
  have eq88033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq87796
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87796
    | exact resolve eq87796 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87796
  have eq88093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq88033
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq88033
    | exact resolve eq88033 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88033
  have eq88121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq88093
    | exact resolve eq88093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88093
  have eq88132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq88121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88121
    | exact resolve eq88121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88121
  have eq88137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq88132
    | exact resolve eq88132 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88132
  have eq88138 : x = y := by
    first
    | (have r₁ := eq88137
       have r₂ := eq27
       grind)
    | exact resolve eq88137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88137
  have eq88139 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq88138
       grind)
    | exact superpose eq88138 eq18
    | exact resolve eq18 eq88138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq88140 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq88138
       grind)
    | exact superpose eq88138 eq24
    | exact resolve eq24 eq88138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq88453 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq88140
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq88140
    | exact resolve eq88140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88140
  have eq88512 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq88453 eq26
    | exact resolve eq26 eq88453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq88453
  have eq89352 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq88512 eq118
    | exact resolve eq118 eq88512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq89361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq88512 eq73990
    | exact resolve eq73990 eq88512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73990 eq88512
  have eq89631 : y = (M.op y x) := by
    first
    | (have r₁ := eq89361
       have r₂ := eq27
       grind)
    | exact resolve eq89361 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89361
  have eq89639 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq89352
       have i₂ := eq88139
       grind)
    | exact superpose eq88139 eq89352
    | exact resolve eq89352 eq88139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89352
  have eq89689 : x = (M.op x x) := by
    first
    | (have i₁ := eq89631
       have i₂ := eq88138
       grind)
    | exact superpose eq88138 eq89631
    | exact resolve eq89631 eq88138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88138 eq89631
  have eq89725 : x = (M.op x y) := by
    first
    | (have i₁ := eq89689
       have i₂ := eq88139
       grind)
    | exact superpose eq88139 eq89689
    | exact resolve eq89689 eq88139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88139 eq89689
  have eq89756 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq89725 eq20
    | exact resolve eq20 eq89725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq90207 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq89756
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq89756
    | exact resolve eq89756 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89756
  have eq90990 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq89725 eq89639
    | exact resolve eq89639 eq89725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89639 eq89725
  have eq90998 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90990 eq15
    | exact resolve eq15 eq90990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90990
  have eq91114 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90998
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq90998
    | exact resolve eq90998 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq90998
  have eq91161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90207 eq91114
    | exact resolve eq91114 eq90207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90207 eq91114
  have eq91205 : False := by grind
  exact eq91205

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op (M.op X2 X1) (M.op X0 X0))) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq117 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq113
    | exact resolve eq113 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq113
  have eq560 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq50
    | exact resolve eq50 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq578 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X1) X1 X2 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq680 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq675
    | exact resolve eq675 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq919 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq53 (M.op X2 X1) (M.op X0 X0)
       grind)
    | exact superpose eq53 eq65
    | (have j0 := eq65 X0 X1 X2
       grind)
    | (have r₁ := eq65 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq65 (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq65 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1014 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op X1 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq919 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq2019 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq633 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq633 X0 X0 X0
       grind)
    | exact superpose eq633 eq633
    | exact resolve eq633 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2074 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq633 X0 X0 X0
       grind)
    | exact superpose eq633 eq50
    | exact resolve eq50 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2075 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq633 X0 X0 X0
       grind)
    | exact superpose eq633 eq51
    | exact resolve eq51 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2084 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq578 (M.op x (M.op x x))
       have i₂ := eq633 x x x
       grind)
    | exact superpose eq633 eq578
    | exact resolve eq578 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq2087 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq669 (M.op x (M.op x x)) x
       have i₂ := eq633 x x x
       grind)
    | exact superpose eq633 eq669
    | exact resolve eq669 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq2253 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq587 X0
       have i₂ := eq2074 X0
       grind)
    | exact superpose eq2074 eq587
    | exact resolve eq587 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2260 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq592 X0 X0
       have i₂ := eq2074 X0
       grind)
    | exact superpose eq2074 eq592
    | exact resolve eq592 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq2281 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq2074 eq591
    | exact resolve eq591 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2294 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq591 eq2281
    | exact resolve eq2281 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq2329 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2253
    | exact resolve eq2253 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2333 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq560 eq2253
    | exact resolve eq2253 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq2253
  have eq2372 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq2329 X0
       grind)
    | exact superpose eq2329 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq2329 X0
       grind)
    | exact resolve eq13 eq2329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329
  have eq2392 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2372 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372
  have eq2441 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2392 (M.op x (M.op x x))
       have i₂ := eq633 x x x
       grind)
    | exact superpose eq633 eq2392
    | exact resolve eq2392 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq2619 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2075 X0
       have i₂ := eq2074 X0
       grind)
    | exact superpose eq2074 eq2075
    | exact resolve eq2075 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2650 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq2075 eq591
    | exact resolve eq591 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2663 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq591 eq2650
    | exact resolve eq2650 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq2650
  have eq2903 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2084 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2084
    | exact resolve eq2084 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq2949 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2903 X0 X1
       have i₂ := eq2074 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq2074 eq2903
    | exact resolve eq2903 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2903
  have eq2966 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2949 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2949
    | exact resolve eq2949 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2949
  have eq3131 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2087 X0 X1
       have i₂ := eq2074 X0
       grind)
    | exact superpose eq2074 eq2087
    | exact resolve eq2087 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074 eq2087
  have eq5393 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X1 X0 X1 X0
       have i₂ := eq680 X0 X1
       grind)
    | exact superpose eq680 eq594
    | exact resolve eq594 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq680
  have eq7095 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq664 (M.op X0 X0) X1 X2
       have i₂ := eq1014 X0 X0
       grind)
    | exact superpose eq1014 eq664
    | exact resolve eq664 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq1014
  have eq7155 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op X0 (M.op X0 X0)) X0)) (k (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7095 X1 X1 X2
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq7095
    | exact resolve eq7095 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7095
  have eq7247 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7155 X0 X1 X2
       have i₂ := eq2441 X0
       grind)
    | exact superpose eq2441 eq7155
    | exact resolve eq7155 eq2441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441 eq7155
  have eq7403 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7247 X1 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq587 X0
       grind)
    | exact superpose eq587 eq7247
    | exact resolve eq7247 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq7247
  have eq48542 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2966 eq14
    | exact resolve eq14 eq2966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2966
  have eq49990 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2019 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2019
    | (have j0 := eq2019 y x X0
       grind)
    | exact resolve eq2019 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq75942 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49990 y
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq49990
    | exact resolve eq49990 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq49990
  have eq76097 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75942
       have i₂ := eq7403 y (M.op y x)
       grind)
    | exact superpose eq7403 eq75942
    | exact resolve eq75942 eq7403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7403 eq75942
  have eq76134 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76097
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq76097
    | exact resolve eq76097 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq76097
  have eq76153 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq48542 eq76134
    | exact resolve eq76134 eq48542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48542 eq76134
  have eq76182 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq76153 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq76153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq76182
    | exact resolve eq76182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76182
  have eq76194 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq76183
       have r₂ := eq27
       grind)
    | exact resolve eq76183 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76183
  have eq76198 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq76194
    | exact resolve eq76194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76194
  have eq76226 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq76198 eq50
    | exact resolve eq50 eq76198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76198
  have eq76632 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq76226 eq5393
    | exact resolve eq5393 eq76226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5393
  have eq76738 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq76632
    | exact resolve eq76632 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76632
  have eq76778 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq76738 eq3131
    | exact resolve eq3131 eq76738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131 eq76738
  have eq85503 : (M.op (σ y) (σ x)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq76778 eq2619
    | exact resolve eq2619 eq76778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619 eq76778
  have eq85609 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2260 eq85503
    | exact resolve eq85503 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260 eq85503
  have eq85633 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq85609 eq76226
    | exact resolve eq76226 eq85609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76226 eq85609
  have eq85708 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq85633
  have eq85714 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq50 eq85708
    | exact resolve eq85708 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq85708
  have eq85716 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq85714 eq27
    | exact resolve eq27 eq85714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85772 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq85714 eq2663
    | exact resolve eq2663 eq85714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq85825 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq85772
    | exact resolve eq85772 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85772
  have eq86278 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq85825 eq2392
    | exact resolve eq2392 eq85825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392 eq85825
  have eq86633 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq85714 eq86278
    | exact resolve eq86278 eq85714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85714 eq86278
  have eq86651 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq86633
  have eq86668 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq86651 eq76153
    | exact resolve eq76153 eq86651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76153 eq86651
  have eq86678 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq86668
  have eq86683 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq86678
       have r₂ := eq85716
       grind)
    | exact resolve eq86678 eq85716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85716 eq86678
  have eq86698 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq86683 eq29
    | exact resolve eq29 eq86683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq86683
  have eq86972 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq86698
    | exact resolve eq86698 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq86698
  have eq86973 : x = (M.op x y) ∨ x = y := by grind
  clear eq86972
  have eq87008 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq86973 eq20
    | exact resolve eq20 eq86973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87126 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq86973 eq2294
    | exact resolve eq2294 eq86973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294 eq86973
  have eq87226 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq87126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87126
    | exact resolve eq87126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87126
  have eq87293 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq87008
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq87008
    | exact resolve eq87008 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87008
  have eq87332 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq87293 eq26
    | exact resolve eq26 eq87293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87293
  have eq87674 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2333 y
       have i₂ := eq87226
       grind)
    | exact superpose eq87226 eq2333
    | exact resolve eq2333 eq87226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333 eq87226
  have eq87805 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq87674
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87674
    | exact resolve eq87674 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87674
  have eq87882 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq87805
    | exact resolve eq87805 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87805
  have eq90216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq87882 eq87332
    | exact resolve eq87332 eq87882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87332 eq87882
  have eq90280 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq90216
  have eq90303 : x = y := by
    first
    | (have r₁ := eq90280
       have r₂ := eq27
       grind)
    | exact resolve eq90280 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90280
  have eq90315 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq90303
       grind)
    | exact superpose eq90303 eq18
    | exact resolve eq18 eq90303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq90316 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq90303
       grind)
    | exact superpose eq90303 eq24
    | exact resolve eq24 eq90303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq90303
  have eq90602 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq90316
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq90316
    | exact resolve eq90316 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq90316
  have eq90661 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq90602 eq26
    | exact resolve eq26 eq90602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq90602
  have eq91502 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq90661 eq117
    | exact resolve eq117 eq90661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq90661
  have eq91802 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq91502
       have i₂ := eq90315
       grind)
    | exact superpose eq90315 eq91502
    | exact resolve eq91502 eq90315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90315 eq91502
  have eq91951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq91802 eq15
    | exact resolve eq15 eq91802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91802
  have eq92067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq91951
    | exact resolve eq91951 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq91951
  have eq92110 : False := by grind
  exact eq92110
