import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq72
    | (have j0 := eq72 (σ X0) (σ X1)
       grind)
    | exact resolve eq72 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq72
    | (have j0 := eq72 (σ x) (σ X0)
       grind)
    | exact resolve eq72 eq35
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
    | (have r₁ := eq110 x
       have r₂ := eq13 X0 x
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
  have eq114 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq43
    | exact resolve eq43 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq115 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq70
    | exact resolve eq70 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq117 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq82
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq82
    | exact resolve eq82 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq118 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq117
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq117
    | exact resolve eq117 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq115
    | exact resolve eq115 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq121 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq114
    | exact resolve eq114 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq122 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq113
  have eq145 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq148 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq145
       have i₂ := eq111 sF1
       grind)
    | exact superpose eq111 eq145
    | exact resolve eq145 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq151 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq111 sF0
       grind)
    | exact superpose eq111 eq148
    | exact resolve eq148 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq173 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq151 eq16
    | exact resolve eq16 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq246 eq151
    | exact resolve eq151 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq251 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq246 eq50
    | exact resolve eq50 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq111 (τ X0)
       grind)
    | exact superpose eq111 eq34
    | exact resolve eq34 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq72 (τ X0) X1
       grind)
    | exact superpose eq72 eq34
    | (have j1 := eq72 (τ X0) X1
       grind)
    | exact resolve eq34 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq335 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq324 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq324
    | exact resolve eq324 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq339 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq335 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq335
    | exact resolve eq335 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq335
  have eq460 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq463 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
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
  have eq464 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
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
  have eq465 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X2 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X2 X2) = (k X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X2 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X1 (M.op X0 X1)
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
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
  have eq482 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
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
  have eq495 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 (M.op X1 X0))) (M.op (M.op X1 X0) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 X0) X2 X3 X4
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
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
  have eq503 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
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
  have eq512 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
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
  have eq516 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) = (k X2 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
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
  have eq518 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
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
  have eq519 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
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
  have eq522 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq519
    | exact resolve eq519 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq523 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq518 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq518
    | exact resolve eq518 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq524 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq517 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq517
    | exact resolve eq517 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq525 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) ∨ (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) = (k X2 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq516 X0 X1 X2
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq516
    | (have j0 := eq516 X0 X1 X2
       grind)
    | exact resolve eq516 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq532 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq503 X0 X1 X2 X3 X4
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq503
    | exact resolve eq503 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq534 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) = (k X2 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq525 X0 X1 X2
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq525
    | (have j0 := eq525 X0 X1 X2
       grind)
    | exact resolve eq525 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq641 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq88 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq88 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq88 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 : G, (σ X1) = (M.op y (M.op (M.op x y) (M.op (σ X0) (σ X1)))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq50 (σ X1)
       have i₂ := eq88 X1 X1
       grind)
    | exact superpose eq88 eq50
    | (have j1 := eq88 X0 X1
       grind)
    | exact resolve eq50 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq657 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq641 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq659 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq751 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0) (σ X0)
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq53
    | exact resolve eq53 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq460 (σ X0)
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq460
    | exact resolve eq460 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq751 X0
       have i₂ := eq122 (M.op X0 X0)
       grind)
    | exact superpose eq122 eq751
    | exact resolve eq751 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq774 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq764 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq764
    | exact resolve eq764 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq856 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq339 X0
       grind)
    | exact superpose eq339 eq16
    | exact resolve eq16 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1030 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq104 eq72
    | (have j0 := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq72 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq1030
    | exact resolve eq1030 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1034 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1031
       have r₂ := eq27
       grind)
    | exact resolve eq1031 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1036 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq1034
    | exact resolve eq1034 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1038 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1036 eq118
    | exact resolve eq118 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1080 : ∀ X0 : G, (M.op y (M.op (τ (M.op (σ x) (σ y))) (M.op X0 X0))) = X0 ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq14
    | exact resolve eq14 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1356 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) = X0 ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1036 eq259
    | exact resolve eq259 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq259 eq51
    | exact resolve eq51 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1411 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq258 eq1388
    | exact resolve eq1388 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1429 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) = X0 ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq258 eq1356
    | exact resolve eq1356 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356
  have eq1512 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq463 (M.op x sF4) (M.op x sF4)
       have i₂ := eq14 (M.op x sF4) sF4 x
       grind)
    | exact superpose eq14 eq463
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1519 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1512 X0
       have i₂ := eq53 X0 sF4
       grind)
    | exact superpose eq53 eq1512
    | exact resolve eq1512 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1619 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq464 (M.op X0 X0) (M.op X1 (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq464
    | exact resolve eq464 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1664 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq259 eq482
    | exact resolve eq482 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1665 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op (σ X0) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq482 X1 (σ X0) X2
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq482
    | exact resolve eq482 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1681 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq482 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq482 X0 X0 X0
       grind)
    | exact superpose eq482 eq482
    | exact resolve eq482 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1712 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq482 X0 X0 X0
       grind)
    | exact superpose eq482 eq14
    | exact resolve eq14 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1713 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq482 X0 X0 X0
       grind)
    | exact superpose eq482 eq50
    | exact resolve eq50 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1724 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq512 (M.op x (M.op x x)) x
       have i₂ := eq482 x x x
       grind)
    | exact superpose eq482 eq512
    | exact resolve eq512 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1751 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq258 eq1664
    | exact resolve eq1664 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664
  have eq4163 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq467 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq467 eq467
    | exact resolve eq467 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq5023 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq258 eq507
    | exact resolve eq507 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq5377 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op X0 (M.op (M.op (σ y) (M.op X0 X0)) X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1429 eq522
    | exact resolve eq522 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq5456 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)))) = (M.op (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq522 (M.op X1 (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq522
    | exact resolve eq522 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5496 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5456 X0 X1
       have i₂ := eq512 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq512 eq5456
    | exact resolve eq5456 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5456
  have eq5516 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq5377 X0
       have i₂ := eq512 X0 sF3
       grind)
    | exact superpose eq512 eq5377
    | exact resolve eq5377 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq5377
  have eq5527 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq522 X0 X1
       grind)
    | exact superpose eq522 eq523
    | exact resolve eq523 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq5528 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq5527 x (M.op (M.op x x) (M.op X0 X0))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq5527
    | exact resolve eq5527 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5624 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq5527
    | (have j0 := eq5527 (σ x) (σ y)
       grind)
    | exact resolve eq5527 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5643 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5527 (M.op x sF4) (M.op X0 X0)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq5527
    | exact resolve eq5527 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5680 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq258 eq5624
    | exact resolve eq5624 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5624
  have eq5707 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq28 eq325
    | exact resolve eq325 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq5763 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq35 eq5707
    | (have j0 := eq5707 X0
       grind)
    | exact resolve eq5707 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq5707
  have eq5782 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq5783 : ∀ X0 : G, (σ (k x (M.op (τ X0) (τ X0)))) = (M.op (σ x) (M.op X0 X0)) ∨ (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5782 (M.op (τ X0) (τ X0))
       have i₂ := eq339 X0
       grind)
    | exact superpose eq339 eq5782
    | exact resolve eq5782 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq5782
  have eq5852 : ∀ X0 : G, (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) = (M.op (σ x) (M.op X0 X0)) ∨ (σ (k x (M.op (τ X0) (τ X0)))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5783 X0
       have i₂ := eq53 (τ X0) (τ X0)
       grind)
    | exact superpose eq53 eq5783
    | (have j0 := eq5783 X0
       grind)
    | exact resolve eq5783 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5783
  have eq6886 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq524 X0 X1 X2 X3
       have i₂ := eq522 X0 X1
       grind)
    | exact superpose eq522 eq524
    | exact resolve eq524 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq6887 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq5527 eq6886
    | exact resolve eq6886 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6886
  have eq7006 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6887 X1 (M.op (M.op X2 X1) (M.op X0 X0)) X2 x
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq6887
    | exact resolve eq6887 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7127 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6887 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq482 x X1 X0
       grind)
    | exact superpose eq482 eq6887
    | exact resolve eq6887 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq7137 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op X2 X1) (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6887 (M.op X2 X1) (M.op X0 X0) (M.op X1 (M.op X2 X1)) (M.op x x)
       have i₂ := eq495 X1 X2 x x X0
       grind)
    | exact superpose eq495 eq6887
    | exact resolve eq6887 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq7161 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6887 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq6887
    | exact resolve eq6887 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7186 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 X1))))) = (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq464 (M.op X0 X1) (M.op X2 (M.op X0 X1))
       have i₂ := eq6887 X0 X1 (M.op X0 X1) X2
       grind)
    | exact superpose eq6887 eq464
    | exact resolve eq464 eq6887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7908 : ∀ X0 : G, (σ y) = (M.op y (M.op (M.op x y) (M.op (σ X0) (σ y)))) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq650 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq650
    | (have j0 := eq650 X0 y
       grind)
    | exact resolve eq650 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq8076 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq532 X0 X1 X2 X3 X4
       have i₂ := eq522 X0 X1
       grind)
    | exact superpose eq522 eq532
    | exact resolve eq532 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq8077 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq5527 eq8076
    | exact resolve eq8076 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8076
  have eq8241 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8077 X1 (M.op (M.op X2 X1) (M.op X0 X0)) X2 X3 x
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq8077
    | exact resolve eq8077 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8438 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0)))) = (M.op (M.op (M.op X1 X2) (M.op (σ y) (σ y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq8077
    | exact resolve eq8077 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq8077
  have eq11640 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 X1
       have i₂ := eq122 X1
       grind)
    | exact superpose eq122 eq659
    | (have j0 := eq659 X0 X1
       grind)
    | exact resolve eq659 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq11641 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11640 X0 X1
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq11640
    | (have j0 := eq11640 X0 X1
       grind)
    | exact resolve eq11640 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq11640
  have eq11715 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (σ (M.op X0 X0)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq11641 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11641
    | (have j0 := eq11641 y X0
       grind)
    | exact resolve eq11641 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11641
  have eq11827 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 X0)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11715 X0
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq11715
    | (have j0 := eq11715 X0
       grind)
    | exact resolve eq11715 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11715
  have eq12310 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) ≠ (M.op (M.op X0 X1) (M.op (M.op X2 X3) (M.op X0 X1))) ∨ (M.op (M.op X2 X3) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (M.op X2 X3) (M.op X0 X1))) ∨ (M.op X3 X3) = (k X3 (M.op (M.op X2 X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq465 (M.op X0 X1) (M.op X2 X3) X3
       have i₂ := eq6887 X0 X1 X3 X2
       grind)
    | (have i₁ := eq465 (M.op X0 X1) (M.op x y) y
       have i₂ := eq6887 X0 X1 X2 X3
       grind)
    | exact superpose eq6887 eq465
    | (have j0 := eq465 (M.op X0 X1) (M.op X2 X3) X3
       grind)
    | exact resolve eq465 eq6887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq6887
  have eq13936 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) = (k X2 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq534 X0 X1 X2
       have i₂ := eq522 X0 X1
       grind)
    | exact superpose eq522 eq534
    | (have j0 := eq534 X0 X1 X2
       grind)
    | exact resolve eq534 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq13937 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k X2 (M.op y (M.op (M.op x y) (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5527 eq13936
    | (have j0 := eq13936 X0 X1 X2
       grind)
    | exact resolve eq13936 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13936
  have eq13938 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) ∨ (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k X2 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13937 X0 X1 X2
       have i₂ := eq522 X0 X1
       grind)
    | exact superpose eq522 eq13937
    | (have j0 := eq13937 X0 X1 X2
       grind)
    | exact resolve eq13937 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq13937
  have eq13939 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op y (M.op (M.op x y) (M.op X0 X1))) ∨ (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 X1)))) = (k X2 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5527 eq13938
    | (have j0 := eq13938 X0 X1 X2
       grind)
    | exact resolve eq13938 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13938
  have eq14054 : ∀ X0 X3 : G, (M.op y (M.op (M.op x y) X0)) ≠ X0 ∨ (M.op X3 (M.op y (M.op (M.op x y) X0))) = (k X3 (M.op y (M.op (M.op x y) X0))) := by
    intro X0 X3
    first
    | (have i₁ := eq13939 x (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq13939
    | exact resolve eq13939 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13939
  have eq15895 : ∀ X0 : G, (τ X0) = (M.op y (M.op (τ (M.op (σ x) (σ y))) (τ (M.op X0 X0)))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1080 (τ X0)
       have i₂ := eq856 X0
       grind)
    | exact superpose eq856 eq1080
    | exact resolve eq1080 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq20417 : ∀ X0 X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op y (M.op y y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1713 eq502
    | exact resolve eq502 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20461 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq20417 x x x
       have i₂ := eq502 y y x x x
       grind)
    | exact superpose eq502 eq20417
    | exact resolve eq20417 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq20417
  have eq21409 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq1724 X0 X1
       have i₂ := eq5516 X0
       grind)
    | exact superpose eq5516 eq1724
    | exact resolve eq1724 eq5516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724 eq5516
  have eq25031 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq5528 eq21409
    | exact resolve eq21409 eq5528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5528 eq21409
  have eq27045 : y = (M.op (M.op x y) (M.op y (M.op (M.op x y) y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq25031 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25031
    | (have j0 := eq25031 y x
       grind)
    | exact resolve eq25031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25031
  have eq27478 : y = (M.op (M.op x y) (M.op y (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1713 eq27045
    | exact resolve eq27045 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27045
  have eq46949 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op y (M.op (τ (M.op (σ x) (σ y))) X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq7006 X0 y y
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq7006
    | exact resolve eq7006 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq51325 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq761 X0
       have i₂ := eq774 X0
       grind)
    | exact superpose eq774 eq761
    | exact resolve eq761 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64585 : ∀ X0 : G, (M.op y (M.op y y)) = (M.op (M.op X0 (M.op x x)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1681 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1681
    | (have j0 := eq1681 y X0 x
       grind)
    | exact resolve eq1681 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64627 : ∀ X0 : G, (M.op (M.op y (M.op y y)) (M.op (M.op y (M.op y y)) (M.op y (M.op y y)))) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq27478 eq1681
    | exact resolve eq1681 eq27478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27478
  have eq65281 : ∀ X0 : G, (M.op (M.op y (M.op y y)) (M.op (M.op y (M.op y y)) (M.op y (M.op y y)))) = (M.op (M.op X0 (M.op y (M.op x y))) y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq246 eq64627
    | exact resolve eq64627 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64627
  have eq65810 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y (M.op y y)))) = (M.op (M.op X0 (M.op y (M.op x y))) y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq65281 X0
       have i₂ := eq1713 (M.op y (M.op y y))
       grind)
    | exact superpose eq1713 eq65281
    | exact resolve eq65281 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65281
  have eq66152 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op y (M.op x y))) y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq464 eq65810
    | exact resolve eq65810 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq65810
  have eq67845 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1411 eq1751
    | exact resolve eq1751 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq67846 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq5680 eq67845
    | exact resolve eq67845 eq5680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67845
  have eq87223 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq15895 eq46949
    | exact resolve eq46949 eq15895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15895 eq46949
  have eq87285 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq87223 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87223
  have eq104113 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1411 eq5023
    | exact resolve eq5023 eq1411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411 eq5023
  have eq104114 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X1) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq5680 eq104113
    | exact resolve eq104113 eq5680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5680 eq104113
  have eq104431 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq5527 eq5496
    | exact resolve eq5496 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5496 eq5527
  have eq104432 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq104431 X0 x
       have i₂ := eq1619 X0 x
       grind)
    | exact superpose eq1619 eq104431
    | exact resolve eq104431 eq1619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619 eq104431
  have eq116721 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X0 (M.op X0 X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7161 X2 (M.op X1 X0) (M.op x (M.op X1 X1)) X3
       have i₂ := eq1681 X0 x X1
       grind)
    | exact superpose eq1681 eq7161
    | exact resolve eq7161 eq1681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq118241 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq7161 eq116721
    | exact resolve eq116721 eq7161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116721
  have eq131716 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7161 X2 (M.op X1 X0) (M.op (M.op x x) (M.op X1 X1)) X3
       have i₂ := eq8241 X0 x x X1
       grind)
    | exact superpose eq8241 eq7161
    | exact resolve eq7161 eq8241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8241
  have eq131739 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq7161 eq131716
    | exact resolve eq131716 eq7161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131716
  have eq323100 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq7908 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7908
    | (have j0 := eq7908 x
       grind)
    | exact resolve eq7908 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7908
  have eq323285 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | exact superpose eq26 eq323100
    | exact resolve eq323100 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323100
  have eq323327 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq323285
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq323285
    | exact resolve eq323285 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323285
  have eq323336 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq323327
    | exact resolve eq323327 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323327
  have eq330091 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (σ y) (σ y))) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq7127 eq8438
    | exact resolve eq8438 eq7127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8438
  have eq330092 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (σ y) (σ y))) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq258 eq330091
    | exact resolve eq330091 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq330091
  have eq331431 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq330092 (M.op sF3 (M.op x x)) x x
       have i₂ := eq52 sF3 x x x
       grind)
    | exact superpose eq52 eq330092
    | exact resolve eq330092 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq330092
  have eq655394 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11827 x
       have i₂ := eq5763 y
       grind)
    | exact superpose eq5763 eq11827
    | (have j1 := eq5763 y
       grind)
    | exact resolve eq11827 eq5763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5763 eq11827
  have eq656254 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq655394
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq655394
    | exact resolve eq655394 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq655394
  have eq656324 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq656254
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq656254
    | exact resolve eq656254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656254
  have eq656382 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq656324
    | exact resolve eq656324 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656324
  have eq656437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq656382
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq656382
    | exact resolve eq656382 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656382
  have eq656464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq656437
    | exact resolve eq656437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656437
  have eq656486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq656464
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq656464
    | exact resolve eq656464 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656464
  have eq656493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq656486
    | exact resolve eq656486 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656486
  have eq656499 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq656493
       have r₂ := eq27
       grind)
    | exact resolve eq656493 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656493
  have eq656503 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq656499
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq656499
    | exact resolve eq656499 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656499
  have eq656506 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq656503 eq1036
    | exact resolve eq1036 eq656503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036 eq656503
  have eq657110 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq656506
  have eq657361 : (τ (σ x)) = (M.op y (M.op (M.op x y) (τ (σ (M.op x y))))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq657110 eq87285
    | exact resolve eq87285 eq657110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87285 eq657110
  have eq657592 : (τ (σ x)) = (M.op y (M.op (M.op x y) (τ (σ (M.op x y))))) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq657361
  have eq657650 : (τ (σ x)) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq657592
    | exact resolve eq657592 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq657592
  have eq657682 : (τ (σ x)) = (M.op y (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq246 eq657650
    | exact resolve eq657650 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657650
  have eq657703 : x = (M.op y (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq657682
    | exact resolve eq657682 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq657682
  have eq688050 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq657703 eq66152
    | exact resolve eq66152 eq657703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66152 eq657703
  have eq688272 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq688050
  have eq688387 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq688272
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq688272
    | exact resolve eq688272 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688272
  have eq688388 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq688387
  have eq688453 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq688388
       grind)
    | exact superpose eq688388 eq120
    | exact resolve eq120 eq688388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq688499 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq761 y
       have i₂ := eq688388
       grind)
    | exact superpose eq688388 eq761
    | exact resolve eq761 eq688388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688500 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq774 y
       have i₂ := eq688388
       grind)
    | exact superpose eq688388 eq774
    | exact resolve eq774 eq688388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq688528 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op x y))) (M.op (σ y) (M.op X1 X1))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1665 y X0 X1
       have i₂ := eq688388
       grind)
    | exact superpose eq688388 eq1665
    | exact resolve eq1665 eq688388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq688762 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104114 y y
       have i₂ := eq688388
       grind)
    | exact superpose eq688388 eq104114
    | (have j0 := eq104114 x y
       grind)
    | exact resolve eq104114 eq688388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104114 eq688388
  have eq688795 : (M.op (σ x) (σ y)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq688762
       have i₂ := eq7186 y (M.op sF0 sF4) sF0
       grind)
    | exact superpose eq7186 eq688762
    | exact resolve eq688762 eq7186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7186 eq688762
  have eq688896 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op x y))) (M.op (σ y) (M.op X1 X1))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq688528 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq688528
    | (have j0 := eq688528 X0 X1
       grind)
    | exact resolve eq688528 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688528
  have eq688911 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq688500
    | exact resolve eq688500 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688500
  have eq688912 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq688499
    | exact resolve eq688499 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688499
  have eq688944 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq688453
    | exact resolve eq688453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688453
  have eq688947 : (M.op (σ x) (σ y)) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104432 eq688795
    | exact resolve eq688795 eq104432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104432 eq688795
  have eq688972 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op x y))) (M.op (σ y) (M.op X1 X1))) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq688896
    | (have j0 := eq688896 X0 X1
       grind)
    | exact resolve eq688896 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688896
  have eq688982 : (σ (M.op y (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq688911
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq688911
    | exact resolve eq688911 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688911
  have eq688983 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq688912
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq688912
    | exact resolve eq688912 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688912
  have eq689001 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq688947
       have i₂ := eq53 y (M.op sF0 sF4)
       grind)
    | exact superpose eq53 eq688947
    | exact resolve eq688947 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq688947
  have eq689011 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq248 eq688982
    | exact resolve eq688982 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688982
  have eq689023 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq689001
       have i₂ := eq4163 y sF0 sF4
       grind)
    | exact superpose eq4163 eq689001
    | exact resolve eq689001 eq4163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689001
  have eq690436 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq688944 eq1712
    | exact resolve eq1712 eq688944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq696131 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op X0 X0)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq688983 eq7161
    | exact resolve eq7161 eq688983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688983
  have eq696385 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7127 eq696131
    | exact resolve eq696131 eq7127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696131
  have eq717230 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 X0)))) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq689023 eq7161
    | exact resolve eq7161 eq689023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689023
  have eq717352 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5643 eq717230
    | exact resolve eq717230 eq5643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5643 eq717230
  have eq912664 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq688944 eq688972
    | exact resolve eq688972 eq688944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688944 eq688972
  have eq913049 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq912664 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912664
  have eq918157 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq689011 eq913049
    | exact resolve eq913049 eq689011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689011 eq913049
  have eq918640 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq918157 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918157
  have eq979578 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op X0 (M.op X0 X0))) (M.op X1 X1)))) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq690436 eq7161
    | exact resolve eq7161 eq690436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690436
  have eq979767 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7161 eq979578
    | exact resolve eq979578 eq7161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979578
  have eq1173984 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (σ (M.op y (M.op (M.op x y) (τ X0)))) ∨ (σ (k x (M.op (τ X0) (τ X0)))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5852 X0
       have i₂ := eq1713 (τ X0)
       grind)
    | exact superpose eq1713 eq5852
    | (have j0 := eq5852 X0
       grind)
    | exact resolve eq5852 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713 eq5852
  have eq1173985 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (σ (k x (τ (M.op X0 X0)))) ∨ (M.op (σ x) (M.op X0 X0)) = (σ (M.op y (M.op (M.op x y) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq1173984 X0
       have i₂ := eq856 X0
       grind)
    | exact superpose eq856 eq1173984
    | (have j0 := eq1173984 X0
       grind)
    | exact resolve eq1173984 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq1173984
  have eq1173986 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (σ (M.op y (M.op (M.op x y) (τ X0)))) ∨ (k (σ x) (M.op X0 X0)) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1173985 X0
       have i₂ := eq42 (M.op X0 X0)
       grind)
    | exact superpose eq42 eq1173985
    | (have j0 := eq1173985 X0
       grind)
    | exact resolve eq1173985 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1173985
  have eq1174014 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq918640 eq1173986
    | exact resolve eq1173986 eq918640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173986
  have eq1174951 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq173 eq1174014
    | exact resolve eq1174014 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq1174014
  have eq1175103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50 eq1174951
    | exact resolve eq1174951 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174951
  have eq1175151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1175103
    | exact resolve eq1175103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175103
  have eq1175181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1175151
    | exact resolve eq1175151 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175151
  have eq1175194 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1175181
       have r₂ := eq27
       grind)
    | exact resolve eq1175181 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175181
  have eq1175200 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1175194
    | exact resolve eq1175194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175194
  have eq1178386 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1178386_13 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op X1 X1))) = X1 := by
      intro X0 X1
      grind
    have f1178386_14 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f1178386_23 : X0 ≠ (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) := by grind
    have f1178386_24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f1178386_26 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) X0) := by
      intro X0
      first
      | (have j0 := f1178386_14 X0
         grind)
      | (have r₁ := f1178386_14 X0
         have r₂ := f1178386_24
         grind)
      | exact resolve f1178386_14 f1178386_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1178386_140 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f1178386_13 X1 X0
         have i₂ := f1178386_26 (M.op X0 X0)
         grind)
      | exact superpose f1178386_26 f1178386_13
      | exact resolve f1178386_13 f1178386_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1178386_444 : X0 ≠ X0 := by
      first
      | (have i₁ := f1178386_23
         have i₂ := f1178386_140 X0 X1
         grind)
      | exact superpose f1178386_140 f1178386_23
      | (have r₁ := f1178386_23
         have r₂ := f1178386_140 X0 X1
         grind)
      | exact resolve f1178386_23 f1178386_140
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1178386_450 : False := by grind
    exact f1178386_450
  clear eq67846
  have eq1178402 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op X0 X0)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq717352 eq7161
    | exact resolve eq7161 eq717352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7161 eq717352
  have eq1179897 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7127 eq1178402
    | exact resolve eq1178402 eq7127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7127 eq1178402
  have eq1180313 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1179897 eq696385
    | exact resolve eq696385 eq1179897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696385 eq1179897
  have eq1181622 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1180313 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180313
  have eq1182530 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1519 eq1181622
    | exact resolve eq1181622 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181622
  have eq1887146 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1887146_14 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f1887146_15 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f1887146_17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
      intro X0 X1
      grind
    have f1887146_19 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
      intro X0 X1
      grind
    have f1887146_20 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
      intro X0 X1
      grind
    have f1887146_21 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f1887146_24 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by grind
    have f1887146_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f1887146_28 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
      intro X0
      first
      | (have j0 := f1887146_15 X0
         grind)
      | (have r₁ := f1887146_15 X0
         have r₂ := f1887146_26
         grind)
      | exact resolve f1887146_15 f1887146_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_29 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) = X0 := by
      intro X0 X1
      first
      | (have j0 := f1887146_14 X0 X1
         grind)
      | (have r₁ := f1887146_14 X0 X1
         have r₂ := f1887146_26
         grind)
      | exact resolve f1887146_14 f1887146_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
      intro X0 X1
      first
      | (have i₁ := f1887146_21 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
         have i₂ := f1887146_21 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
         grind)
      | exact superpose f1887146_21 f1887146_21
      | exact resolve f1887146_21 f1887146_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_94 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
      intro X0
      first
      | (have j0 := f1887146_19 X0 X0
         grind)
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_97 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
      intro X0
      first
      | (have j0 := f1887146_94 X0
         have j1 := f1887146_20 X0 X0
         grind)
      | (have r₁ := f1887146_94 x
         have r₂ := f1887146_20 X0 x
         grind)
      | exact resolve f1887146_94 f1887146_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_103 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
      intro X0
      first
      | (have i₁ := f1887146_17 X0 X0
         have i₂ := f1887146_97 (σ X0)
         grind)
      | exact superpose f1887146_97 f1887146_17
      | exact resolve f1887146_17 f1887146_97
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
      intro X0
      first
      | (have i₁ := f1887146_103 X0
         have i₂ := f1887146_97 X0
         grind)
      | exact superpose f1887146_97 f1887146_103
      | exact resolve f1887146_103 f1887146_97
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_127 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
      intro X0
      first
      | (have i₁ := f1887146_29 (M.op (σ (M.op x y)) (σ (M.op x y))) X0
         have i₂ := f1887146_28 (σ (M.op x y))
         grind)
      | exact superpose f1887146_28 f1887146_29
      | exact resolve f1887146_29 f1887146_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_139 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op y y))) := by
      intro X0
      first
      | (have i₁ := f1887146_127 X0
         have i₂ := f1887146_112 y
         grind)
      | exact superpose f1887146_112 f1887146_127
      | exact resolve f1887146_127 f1887146_112
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_147 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op y y))) := by
      intro X0
      first
      | (have i₁ := f1887146_139 X0
         have i₂ := f1887146_112 (M.op x y)
         grind)
      | exact superpose f1887146_112 f1887146_139
      | exact resolve f1887146_139 f1887146_112
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_153 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op y y))) = (σ (M.op y (M.op x y))) := by
      intro X0
      first
      | (have i₁ := f1887146_147 X0
         have i₂ := f1887146_33 x y
         grind)
      | exact superpose f1887146_33 f1887146_147
      | exact resolve f1887146_147 f1887146_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_185 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op y y))) := by
      first
      | (have i₁ := f1887146_24
         have i₂ := f1887146_112 y
         grind)
      | exact superpose f1887146_112 f1887146_24
      | exact resolve f1887146_24 f1887146_112
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_188 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (σ (M.op y (M.op x y))) := by
      first
      | (have i₁ := f1887146_185
         have i₂ := f1887146_153 X0
         grind)
      | exact superpose f1887146_153 f1887146_185
      | exact resolve f1887146_185 f1887146_153
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_190 : (σ (M.op (M.op x y) (M.op x y))) ≠ (σ (M.op y (M.op x y))) := by
      first
      | (have i₁ := f1887146_188
         have i₂ := f1887146_112 (M.op x y)
         grind)
      | exact superpose f1887146_112 f1887146_188
      | exact resolve f1887146_188 f1887146_112
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_191 : (σ (M.op y (M.op x y))) ≠ (σ (M.op y (M.op x y))) := by
      first
      | (have i₁ := f1887146_190
         have i₂ := f1887146_33 x y
         grind)
      | exact superpose f1887146_33 f1887146_190
      | exact resolve f1887146_190 f1887146_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1887146_192 : False := by grind
    exact f1887146_192
  clear eq918640 eq1178386
  have eq1887943 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1887146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887146
  have eq2371719 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op (σ (M.op x y)) (σ (M.op x y))))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1887943 eq7137
    | exact resolve eq7137 eq1887943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7137 eq1887943
  have eq2372443 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op (σ (M.op x y)) (σ (M.op x y))))) = (M.op (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1519 eq2371719
    | exact resolve eq2371719 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519 eq2371719
  have eq2372534 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq50 eq2372443
    | exact resolve eq2372443 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2372443
  have eq2610239 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1182530 eq2372534
    | exact resolve eq2372534 eq1182530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182530 eq2372534
  have eq2610775 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2610239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610239
  have eq2869770 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) ≠ (M.op X1 (M.op (M.op X2 X3) (M.op X0 X1))) ∨ (M.op (M.op X2 X3) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (M.op X2 X3) (M.op X0 X1))) ∨ (M.op X3 X3) = (k X3 (M.op (M.op X2 X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12310 X0 X1 X2 X3
       have i₂ := eq4163 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq4163 eq12310
    | (have j0 := eq12310 X0 X1 X2 X3
       grind)
    | (have r₁ := eq12310 X1 y x y
       have r₂ := eq4163 (M.op x y) X1 y
       grind)
    | exact resolve eq12310 eq4163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12310
  have eq2869771 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) ≠ (M.op X1 (M.op (M.op X2 X3) (M.op X0 X1))) ∨ (M.op (M.op X2 X3) (M.op X0 X1)) = (M.op X1 (M.op (M.op X2 X3) (M.op X0 X1))) ∨ (M.op X3 X3) = (k X3 (M.op (M.op X2 X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2869770 X0 X1 X2 X3
       have i₂ := eq4163 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq4163 eq2869770
    | (have j0 := eq2869770 X0 X1 X2 X3
       grind)
    | exact resolve eq2869770 eq4163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4163 eq2869770
  have eq4301567 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op x y)) X0) X1) = (M.op (M.op X2 X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118241 X0 X2 X1
       have i₂ := eq979767 X0 X1
       grind)
    | (have i₁ := eq118241 (σ (M.op x y)) X1 X1
       have i₂ := eq979767 (σ (M.op x y)) X1
       grind)
    | exact superpose eq979767 eq118241
    | exact resolve eq118241 eq979767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118241 eq979767
  have eq4396151 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2610775 X0
       have i₂ := eq4301567 (M.op X0 sF4) sF3 sF1
       grind)
    | exact superpose eq4301567 eq2610775
    | exact resolve eq2610775 eq4301567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610775 eq4301567
  have eq4403212 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq4396151 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396151
  have eq4802315 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq331431 X0
       have i₂ := eq131739 sF4 sF3 (M.op sF3 (M.op X0 X0))
       grind)
    | exact superpose eq131739 eq331431
    | exact resolve eq331431 eq131739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331431
  have eq5086531 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq323336 eq14054
    | exact resolve eq14054 eq323336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14054 eq323336
  have eq5087339 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq5086531 X0
       grind)
    | (have r₁ := eq5086531 X0
       have r₂ := eq1175200
       grind)
    | exact resolve eq5086531 eq1175200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175200 eq5086531
  have eq5087509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq104 eq5087339
    | exact resolve eq5087339 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq5088318 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j0 := eq5087339 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5087339
  have eq5088319 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq5088318
       have r₂ := eq26
       grind)
    | exact resolve eq5088318 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088318
  have eq5088600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq5087509
       have r₂ := eq27
       grind)
    | exact resolve eq5087509 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5087509
  have eq5088736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq5088600
    | exact resolve eq5088600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088600
  have eq5088814 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq5088736
       have r₂ := eq27
       grind)
    | exact resolve eq5088736 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088736
  have eq5088910 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5088319 eq57
    | exact resolve eq57 eq5088319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq5089216 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq5088814
       grind)
    | exact superpose eq5088814 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq5088814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5089228 : y = (M.op y (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq460 y
       have i₂ := eq5088814
       grind)
    | exact superpose eq5088814 eq460
    | exact resolve eq460 eq5088814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq5089437 : (σ y) = (M.op (σ y) (σ (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq51325 y
       have i₂ := eq5088814
       grind)
    | exact superpose eq5088814 eq51325
    | exact resolve eq51325 eq5088814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51325
  have eq5090197 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq248 eq5089437
    | exact resolve eq5089437 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq5089437
  have eq5090528 : (σ y) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq5090197
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5090197
    | exact resolve eq5090197 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5090197
  have eq5096975 : (σ (M.op x y)) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq5090528 eq4802315
    | exact resolve eq4802315 eq5090528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4802315 eq5090528
  have eq5104140 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5096975
       have i₂ := eq131739 sF4 sF0 sF3
       grind)
    | exact superpose eq131739 eq5096975
    | exact resolve eq5096975 eq131739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131739 eq5096975
  have eq5385645 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op x x)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq64585 X0
       have i₂ := eq5088814
       grind)
    | exact superpose eq5088814 eq64585
    | exact resolve eq64585 eq5088814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64585
  have eq5385970 : (M.op y (M.op (M.op x y) (M.op x y))) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq5385645 eq7006
    | exact resolve eq7006 eq5385645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7006 eq5385645
  have eq5386545 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq246 eq5385970
    | exact resolve eq5385970 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq5385970
  have eq5386572 : y = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq5089228 eq5386545
    | exact resolve eq5386545 eq5089228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5089228 eq5386545
  have eq5386624 : (M.op (M.op x y) y) ≠ (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) ∨ y = (M.op (M.op x y) y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq5386572 eq2869771
    | exact resolve eq2869771 eq5386572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2869771 eq5386572
  have eq5387413 : (M.op x y) ≠ (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq251 eq5386624
    | exact resolve eq5386624 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq5386624
  have eq5387628 : (M.op x y) ≠ (M.op y y) ∨ y = (M.op (M.op x y) y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq20461 eq5387413
    | exact resolve eq5387413 eq20461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5387413
  have eq5387767 : y = (M.op (M.op x y) y) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq5387628
       have r₂ := eq5088814
       grind)
    | exact resolve eq5387628 eq5088814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5387628
  have eq5387847 : y = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq20461 eq5387767
    | exact resolve eq5387767 eq20461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20461 eq5387767
  have eq5387887 : y = (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq5387847
       have i₂ := eq5088814
       grind)
    | exact superpose eq5088814 eq5387847
    | exact resolve eq5387847 eq5088814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088814 eq5387847
  have eq5387906 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5387887
       have i₂ := eq5088910
       grind)
    | exact superpose eq5088910 eq5387887
    | exact resolve eq5387887 eq5088910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088910 eq5387887
  have eq5408438 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (τ (M.op (σ x) (σ y)))))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq761 x
       have i₂ := eq5387906
       grind)
    | exact superpose eq5387906 eq761
    | exact resolve eq761 eq5387906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq5387906
  have eq5409748 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5408438
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq5408438
    | exact resolve eq5408438 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408438
  have eq5410028 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5409748
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5409748
    | exact resolve eq5409748 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5409748
  have eq5422310 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5410028 eq4403212
    | exact resolve eq4403212 eq5410028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4403212
  have eq5423149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5422310
    | exact resolve eq5422310 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5422310
  have eq5423368 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5423149
       have r₂ := eq27
       grind)
    | exact resolve eq5423149 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5423149
  have eq5424421 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5423368 eq5410028
    | exact resolve eq5410028 eq5423368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5410028 eq5423368
  have eq5424423 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq5424421
  have eq5424427 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5424423
    | exact resolve eq5424423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5424423
  have eq5424676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5424427 eq5104140
    | exact resolve eq5104140 eq5424427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5104140 eq5424427
  have eq5425476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5424676
    | exact resolve eq5424676 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5424676
  have eq5425643 : y = (M.op x y) := by
    first
    | (have r₁ := eq5425476
       have r₂ := eq27
       grind)
    | exact resolve eq5425476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5425476
  have eq5427583 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq5425643 eq5089216
    | (have j0 := eq5089216 X0
       grind)
    | (have r₁ := eq5089216 X0
       have r₂ := eq5425643
       grind)
    | exact resolve eq5089216 eq5425643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5089216 eq5425643
  have eq5427660 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq5427583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5427583
  have eq5519983 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq5427660 x
       grind)
    | exact superpose eq5427660 eq44
    | exact resolve eq44 eq5427660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5427660
  have eq5521012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5088319 eq5519983
    | exact resolve eq5519983 eq5088319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088319 eq5519983
  have eq5521541 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5521012
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5521012
    | exact resolve eq5521012 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5521012
  have eq5521908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5521541
    | exact resolve eq5521541 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5521541
  have eq5522176 : False := by grind
  exact eq5522176

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq36
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq36
  have eq95 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq103 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq315 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq318 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq315 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq315 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq315 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq315 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq315 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq338 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq318 X1 (τ X0)
       grind)
    | exact superpose eq318 eq28
    | (have j1 := eq318 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq28 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq339 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq318 (σ X1) (σ X0)
       grind)
    | exact superpose eq318 eq15
    | (have j1 := eq318 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq44296 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq338 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq338
    | exact resolve eq338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq44460 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44296 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq44296
    | (have j0 := eq44296 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq44296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44296
  have eq52875 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq339 x y
       grind)
    | exact superpose eq339 eq16
    | (have j1 := eq339 x y
       grind)
    | exact resolve eq16 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq54796 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52875
       have i₂ := eq44460 x y
       grind)
    | exact superpose eq44460 eq52875
    | (have j1 := eq44460 (σ x) (σ y)
       grind)
    | (have r₁ := eq52875
       have r₂ := eq44460 x y
       grind)
    | (have r₁ := eq52875
       have r₂ := eq44460 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq52875
       have r₂ := eq44460 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq52875 eq44460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44460 eq52875
  have eq54797 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq54796
  have eq55380 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq54797
       grind)
    | exact superpose eq54797 eq10
    | exact resolve eq10 eq54797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54797
  have eq55452 : x = y ∨ x = y := by
    first
    | (have i₁ := eq55380
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq55380
    | exact resolve eq55380 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55380
  have eq55453 : x = y := by grind
  clear eq55452
  have eq57246 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55453
       grind)
    | exact superpose eq55453 eq16
    | exact resolve eq16 eq55453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55453
  have eq57247 : False := by grind
  exact eq57247

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_y_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
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
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq69 : y ≠ (M.op x y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
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
  have eq92 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq88
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq92
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq117
  have eq121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq120
  have eq160 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq53 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) := by
    first
    | exact superpose eq211 eq121
    | exact resolve eq121 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq275 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq286 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq275
    | exact resolve eq275 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq288 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq286
  have eq606 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq16
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq683 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq55 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (M.op X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 (σ X0) X1 X2 X3
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq55
    | exact resolve eq55 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq56 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq55 X0 x x X3
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq1054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1054
    | exact resolve eq1054 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1058 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1055
       have r₂ := eq28
       grind)
    | exact resolve eq1055 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1060 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1058
    | exact resolve eq1058 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1064 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1060 eq70
    | (have r₁ := eq70
       have r₂ := eq1060
       grind)
    | exact resolve eq70 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1060
  have eq1071 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1064
  have eq1072 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1071
  have eq1155 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1072 eq102
    | exact resolve eq102 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1156 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1072 eq99
    | exact resolve eq99 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1072
  have eq1159 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1155
  have eq1163 : x = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1156
    | exact resolve eq1156 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1166 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1163
       have r₂ := eq69
       grind)
    | exact resolve eq1163 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1163
  have eq1169 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq1166
       grind)
    | exact superpose eq1166 eq87
    | exact resolve eq87 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1166
  have eq1174 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1169
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1169
    | exact resolve eq1169 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1275 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1174 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1276 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1275
  have eq1280 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1276
    | exact resolve eq1276 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1283 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1280
    | exact resolve eq1280 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1286 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1159 eq30
    | exact resolve eq30 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1310 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq1286
    | exact resolve eq1286 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1311 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1310
  have eq1315 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1311 eq29
    | exact resolve eq29 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1336 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1315
    | exact resolve eq1315 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1422 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1336 eq21
    | exact resolve eq21 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1424 : ∀ X0 : G, (M.op y (M.op y (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1336 eq53
    | exact resolve eq53 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1432 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1336 eq214
    | exact resolve eq214 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1446 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1432
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq1432
    | exact resolve eq1432 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1432
  have eq1453 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1422
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1422
    | exact resolve eq1422 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1457 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1453 eq27
    | exact resolve eq27 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X0))
       have i₂ := eq709 X0 X0 X0
       grind)
    | exact superpose eq709 eq53
    | exact resolve eq53 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1813 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 (M.op X0 X0))
       have i₂ := eq709 X0 X0 X0
       grind)
    | exact superpose eq709 eq54
    | exact resolve eq54 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1863 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1283 eq28
    | exact resolve eq28 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1877 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1453 eq1863
    | (have r₁ := eq1863
       have r₂ := eq1453
       grind)
    | exact resolve eq1863 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq1878 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1877
  have eq1879 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1878
  have eq4465 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq687 X0 X0 (M.op X0 X0) x
       have i₂ := eq709 x X0 X0
       grind)
    | exact superpose eq709 eq687
    | exact resolve eq687 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq4664 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq687 (σ X0) (σ X0) (σ (M.op X0 X0)) (M.op x x)
       have i₂ := eq728 X0 x x (σ X0)
       grind)
    | exact superpose eq728 eq687
    | exact resolve eq687 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq728
  have eq4678 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4664 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq4664
    | exact resolve eq4664 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq4664
  have eq5108 : ∀ X0 : G, (τ X0) = (M.op y (M.op y (τ (M.op X0 X0)))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1424 (τ X0)
       have i₂ := eq606 X0
       grind)
    | exact superpose eq606 eq1424
    | exact resolve eq1424 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq1424
  have eq22250 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op y X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1336 eq1812
    | exact resolve eq1812 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq22477 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1453 eq1813
    | exact resolve eq1813 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453 eq1813
  have eq26029 : ∀ X0 : G, (M.op X0 (M.op y (M.op y X0))) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq683 X0
       have i₂ := eq22250 X0
       grind)
    | (have i₁ := eq683 y
       have i₂ := eq22250 y
       grind)
    | exact superpose eq22250 eq683
    | exact resolve eq683 eq22250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22250
  have eq34021 : (τ (σ y)) = (M.op y (M.op y (τ (M.op (σ (M.op x y)) (σ (M.op x y)))))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1446 eq5108
    | exact resolve eq5108 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446 eq5108
  have eq34064 : (τ (σ y)) = (M.op y (M.op y (τ (M.op (σ (M.op x y)) (σ (M.op x y)))))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq34021
  have eq34075 : (τ (σ y)) = (M.op y (M.op y (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq160 eq34064
    | exact resolve eq34064 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34064
  have eq34084 : (τ (σ y)) = (M.op y (M.op y (M.op y (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq211 eq34075
    | exact resolve eq34075 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34075
  have eq34089 : y = (M.op y (M.op y (M.op y (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq34084
    | exact resolve eq34084 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq34084
  have eq34163 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq34089 eq26029
    | exact resolve eq26029 eq34089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26029 eq34089
  have eq34200 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq34163
  have eq37673 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq22477 eq734
    | exact resolve eq734 eq22477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22477
  have eq37733 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq37673 x x x
       have i₂ := eq734 sF1 sF1 x x x
       grind)
    | exact superpose eq734 eq37673
    | exact resolve eq37673 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37673
  have eq37797 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1879 eq37733
    | exact resolve eq37733 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37733
  have eq37838 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq37797
  have eq38361 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq37838 eq1457
    | exact resolve eq1457 eq37838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq38396 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq38361
  have eq38469 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38396 eq4465
    | exact resolve eq4465 eq38396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4465 eq38396
  have eq38555 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1879 eq38469
    | exact resolve eq38469 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879 eq38469
  have eq38610 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq38555
  have eq38679 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38610 eq37838
    | exact resolve eq37838 eq38610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37838 eq38610
  have eq38718 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq38679
  have eq38727 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38718 eq160
    | exact resolve eq160 eq38718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq38718
  have eq38870 : (τ (σ x)) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq211 eq38727
    | exact resolve eq38727 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq38727
  have eq38873 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq38870
    | exact resolve eq38870 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38870
  have eq39164 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38873 eq34200
    | exact resolve eq34200 eq38873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34200 eq38873
  have eq39204 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq39164
  have eq39227 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39204
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq39204
    | exact resolve eq39204 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39204
  have eq39228 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq39227
  have eq39234 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39228 eq29
    | exact resolve eq29 eq39228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq39228
  have eq39486 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq39234
    | exact resolve eq39234 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq39234
  have eq39487 : x = (M.op x y) ∨ x = y := by grind
  clear eq39486
  have eq39568 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39487 eq21
    | exact resolve eq21 eq39487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39640 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq39487 eq1812
    | exact resolve eq1812 eq39487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812 eq39487
  have eq39785 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq39568
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39568
    | exact resolve eq39568 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39568
  have eq39800 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq39785 eq27
    | exact resolve eq27 eq39785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39785
  have eq73221 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq683 X0
       have i₂ := eq39640 X0
       grind)
    | exact superpose eq39640 eq683
    | exact resolve eq683 eq39640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq39640
  have eq73544 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 X1) (M.op y y)) y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq734 y x X0 X1 y
       have i₂ := eq73221 y
       grind)
    | exact superpose eq73221 eq734
    | exact resolve eq734 eq73221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq73221
  have eq73634 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq73544 x x
       have i₂ := eq745 y (M.op x x)
       grind)
    | exact superpose eq745 eq73544
    | exact resolve eq73544 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq73544
  have eq73635 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq73634
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73634
    | exact resolve eq73634 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73634
  have eq73716 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4678 y
       have i₂ := eq73635
       grind)
    | exact superpose eq73635 eq4678
    | exact resolve eq4678 eq73635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4678 eq73635
  have eq73786 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq73716
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq73716
    | exact resolve eq73716 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73716
  have eq73821 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq73786
    | exact resolve eq73786 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73786
  have eq74134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq73821 eq39800
    | exact resolve eq39800 eq73821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39800 eq73821
  have eq74176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq74134
  have eq74186 : x = y := by
    first
    | (have r₁ := eq74176
       have r₂ := eq28
       grind)
    | exact resolve eq74176 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74176
  have eq74201 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq74186
       grind)
    | exact superpose eq74186 eq19
    | exact resolve eq19 eq74186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq74202 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq74186
       grind)
    | exact superpose eq74186 eq25
    | exact resolve eq25 eq74186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq74186
  have eq74364 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq74202
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq74202
    | exact resolve eq74202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq74202
  have eq74391 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq74364 eq27
    | exact resolve eq27 eq74364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq74364
  have eq75016 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq74391 eq68
    | exact resolve eq68 eq74391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq74391
  have eq75181 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq75016
       have i₂ := eq74201
       grind)
    | exact superpose eq74201 eq75016
    | exact resolve eq75016 eq74201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74201 eq75016
  have eq75226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75181 eq15
    | exact resolve eq15 eq75181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75181
  have eq75305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq75226
    | exact resolve eq75226 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq75226
  have eq75330 : False := by grind
  exact eq75330

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
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
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq26
    | exact resolve eq26 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq97
    | exact resolve eq97 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq103
    | exact resolve eq103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq103
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq163 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138 y x
       grind)
    | exact superpose eq138 eq16
    | (have j1 := eq138 y x
       grind)
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq678 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq163
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq163
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq163
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq163
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq163 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq679 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq678
  have eq29948 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq679
       grind)
    | exact superpose eq679 eq16
    | exact resolve eq16 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq29949 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq29948
       have r₂ := eq23 x
       grind)
    | exact resolve eq29948 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29948
  have eq659664 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29949
       grind)
    | exact superpose eq29949 eq10
    | exact resolve eq10 eq29949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29949
  have eq660092 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq659664
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq659664
    | exact resolve eq659664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659664
  have eq660111 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq660092
       grind)
    | exact superpose eq660092 eq16
    | exact resolve eq16 eq660092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660092
  have eq660112 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq660111
       have r₂ := eq23 x
       grind)
    | exact resolve eq660111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq660111
  have eq660233 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq660112
       grind)
    | exact superpose eq660112 eq10
    | exact resolve eq10 eq660112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660112
  have eq660793 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq660233
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq660233
    | exact resolve eq660233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660233
  have eq660794 : y = (M.op x x) := by grind
  clear eq660793
  have eq660961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq660794
       grind)
    | exact superpose eq660794 eq104
    | exact resolve eq104 eq660794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq660794
  have eq661705 : False := by grind
  exact eq661705

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxy_pxx_pyx_Equation960 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq107 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
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
  have eq110 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq107 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq107
    | exact resolve eq107 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq110
    | exact resolve eq110 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq118 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq107 X0 X0
       grind)
    | exact superpose eq107 eq116
    | exact resolve eq116 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq116
  have eq299 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq304 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq299 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq299
    | (have j0 := eq299 X0 X1
       grind)
    | exact resolve eq299 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq3566 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq304
    | (have j0 := eq304 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq304 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq43380 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3566 x y
       grind)
    | exact superpose eq3566 eq16
    | (have j1 := eq3566 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3566 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3566 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq3566 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq43461 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq43380
  have eq405566 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq43461
       grind)
    | exact superpose eq43461 eq10
    | exact resolve eq10 eq43461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43461
  have eq405916 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq405566
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq405566
    | exact resolve eq405566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405566
  have eq405917 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq405916
  have eq406062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq118 x
       have i₂ := eq405917
       grind)
    | exact superpose eq405917 eq118
    | exact resolve eq118 eq405917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq405917
  have eq406553 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq406062
       have r₂ := eq16
       grind)
    | exact resolve eq406062 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406062
  have eq406593 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq406553
       grind)
    | exact superpose eq406553 eq10
    | exact resolve eq10 eq406553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406553
  have eq406853 : x = y ∨ x = y := by
    first
    | (have i₁ := eq406593
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq406593
    | exact resolve eq406593 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406593
  have eq406854 : x = y := by grind
  clear eq406853
  have eq406872 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq406854
       grind)
    | exact superpose eq406854 eq16
    | exact resolve eq16 eq406854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406854
  have eq406873 : False := by grind
  exact eq406873

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pxx_x_pxy_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
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
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq44
    | exact resolve eq44 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq50
    | exact resolve eq50 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq71
    | exact resolve eq71 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op y y) = (M.op y x) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq90 : (M.op y y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq89
    | exact resolve eq89 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq111 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq115 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq69 sF3
       grind)
    | exact superpose eq69 eq111
    | exact resolve eq111 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq115
    | exact resolve eq115 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq151 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq10
    | exact resolve eq10 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq762 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq763 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq56 X2 X0 X1 x
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op X1 (M.op X0 x)) y)) := by
    intro X0 X1
    first
    | exact superpose eq761 eq14
    | exact resolve eq14 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X1 : G, (M.op (M.op x (M.op x y)) (M.op y (M.op (M.op x (M.op x y)) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq761 eq14
    | exact resolve eq14 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq980 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq243 eq51
    | exact resolve eq51 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1019 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq980 eq56
    | exact resolve eq56 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq1021 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1019 X0 X1 x
       have i₂ := eq14 (M.op sF0 X0) y x
       grind)
    | exact superpose eq14 eq1019
    | exact resolve eq1019 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1101 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq248 eq52
    | exact resolve eq52 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1122 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1101 eq56
    | exact resolve eq56 eq1101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 X0 X1 x
       have i₂ := eq14 (M.op sF4 X0) sF3 x
       grind)
    | exact superpose eq14 eq1122
    | exact resolve eq1122 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1214 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq759 X1 (σ X0) (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq759
    | exact resolve eq759 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X1) X2) = (M.op (M.op X3 X1) (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq759 (M.op (M.op X4 X1) X2) X3 X1
       have i₂ := eq56 X2 X1 X4 X0
       grind)
    | exact superpose eq56 eq759
    | exact resolve eq759 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1238 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq759 (σ X0) X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq759
    | exact resolve eq759 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X1) X2) = (M.op (M.op X4 X1) X2) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1227 x X1 X2 X4 X3
       have i₂ := eq14 X2 X1 x
       grind)
    | exact superpose eq14 eq1227
    | exact resolve eq1227 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1418 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X3))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq763 (M.op X1 (M.op X1 X0)) (M.op x X1) X3
       have i₂ := eq759 X0 x X1
       grind)
    | exact superpose eq759 eq763
    | exact resolve eq763 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq1420 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq762 eq763
    | exact resolve eq763 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq1593 : ∀ X1 X2 : G, (M.op y X1) = (M.op (M.op X2 (M.op x (M.op x y))) X1) := by
    intro X1 X2
    first
    | exact superpose eq761 eq1288
    | exact resolve eq1288 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq1600 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1288 (σ X0) X1 (σ X0) X2
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq1288
    | exact resolve eq1288 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12400 : (σ (k (M.op y y) (M.op y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq151 (M.op y y)
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq151
    | exact resolve eq151 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq151
  have eq12502 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq12400
       have i₂ := eq69 (M.op sF3 sF3)
       grind)
    | exact superpose eq69 eq12400
    | exact resolve eq12400 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12400
  have eq12513 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq12502
       have i₂ := eq69 (M.op y y)
       grind)
    | exact superpose eq69 eq12502
    | exact resolve eq12502 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq12502
  have eq12517 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1124 eq12513
    | exact resolve eq12513 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124 eq12513
  have eq12520 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq248 eq12517
    | exact resolve eq12517 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq12517
  have eq12521 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (σ (M.op (M.op x y) (M.op y y))) := by
    first
    | (have i₁ := eq12520
       have i₂ := eq1021 (M.op y y) y
       grind)
    | exact superpose eq1021 eq12520
    | exact resolve eq12520 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12520
  have eq12522 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (σ (M.op y (M.op (M.op x y) y))) := by
    first
    | exact superpose eq243 eq12521
    | exact resolve eq12521 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq12521
  have eq15388 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op y (M.op (M.op x (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq788 eq763
    | exact resolve eq763 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq788
  have eq16268 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1420 X1
       have i₂ := eq1288 sF4 (M.op sF3 X1) sF2 x
       grind)
    | (have i₁ := eq1420 X1
       have i₂ := eq1288 sF4 (M.op sF3 X1) x sF2
       grind)
    | exact superpose eq1288 eq1420
    | exact resolve eq1420 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq120548 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq14
    | exact resolve eq14 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq120742 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq120548 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq120548
    | exact resolve eq120548 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120548
  have eq120892 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq120742 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq120742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120742
  have eq120904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq120892
    | exact resolve eq120892 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120892
  have eq120917 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq120904
       have r₂ := eq28
       grind)
    | exact resolve eq120904 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120904
  have eq120982 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq120917 eq14
    | exact resolve eq14 eq120917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120917
  have eq121176 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq120982 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq120982
    | exact resolve eq120982 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120982
  have eq121316 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq121176 eq74
    | exact resolve eq74 eq121176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121176
  have eq121555 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq30 eq121316
    | exact resolve eq121316 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121316
  have eq121556 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq121555
  have eq121945 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op y (M.op (M.op X0 y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq787 x x
       have i₂ := eq121556
       grind)
    | exact superpose eq121556 eq787
    | exact resolve eq787 eq121556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq121976 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1238 x X0
       have i₂ := eq121556
       grind)
    | exact superpose eq121556 eq1238
    | exact resolve eq1238 eq121556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq122146 : (σ x) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq121976 x
       have i₂ := eq1600 x (M.op (σ x) (σ y)) x
       grind)
    | exact superpose eq1600 eq121976
    | exact resolve eq121976 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600 eq121976
  have eq122156 : (M.op x (M.op x y)) = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq121945 x
       have i₂ := eq1021 y x
       grind)
    | (have i₁ := eq121945 x
       have i₂ := eq1021 y x
       grind)
    | exact superpose eq1021 eq121945
    | (have j0 := eq121945 x
       grind)
    | exact resolve eq121945 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121945
  have eq122193 : (σ x) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq122146
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq122146
    | exact resolve eq122146 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122146
  have eq122207 : (σ x) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq122193
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq122193
    | exact resolve eq122193 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122193
  have eq122209 : (σ x) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq122207
    | exact resolve eq122207 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122207
  have eq122211 : (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq122209
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq122209
    | exact resolve eq122209 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq122209
  have eq127687 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq122211 eq16268
    | exact resolve eq16268 eq122211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16268 eq122211
  have eq137156 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op x X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1418 x x x
       have i₂ := eq121556
       grind)
    | exact superpose eq121556 eq1418
    | exact resolve eq1418 eq121556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418 eq121556
  have eq138062 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op x X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq137156 X0
       have i₂ := eq1021 (M.op (M.op x y) (M.op x X0)) x
       grind)
    | (have i₁ := eq137156 X0
       have i₂ := eq1021 (M.op (M.op x y) (M.op x X0)) x
       grind)
    | exact superpose eq1021 eq137156
    | (have j0 := eq137156 X0
       grind)
    | exact resolve eq137156 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137156
  have eq138266 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op x X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq138062 X0
       have i₂ := eq1021 (M.op x X0) x
       grind)
    | (have i₁ := eq138062 X0
       have i₂ := eq1021 (M.op x X0) x
       grind)
    | exact superpose eq1021 eq138062
    | (have j0 := eq138062 X0
       grind)
    | exact resolve eq138062 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq138062
  have eq144053 : (σ (M.op x (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq122156 eq12522
    | exact resolve eq12522 eq122156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12522 eq122156
  have eq256182 : (σ y) = (M.op (σ y) (σ (M.op x (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq144053 eq1101
    | exact resolve eq1101 eq144053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101 eq144053
  have eq300908 : (σ (M.op x (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq256182 eq127687
    | exact resolve eq127687 eq256182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127687 eq256182
  have eq301142 : (σ (M.op x (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq300908
  have eq301285 : (σ (M.op x (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq301142
    | exact resolve eq301142 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301142
  have eq301372 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq301285
       have i₂ := eq1288 sF4 sF4 sF2 x
       grind)
    | (have i₁ := eq301285
       have i₂ := eq1288 sF4 sF4 x sF2
       grind)
    | exact superpose eq1288 eq301285
    | exact resolve eq301285 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq301285
  have eq301811 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq301372 eq301372
    | exact resolve eq301372 eq301372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301372
  have eq302131 : (σ (M.op x (M.op x y))) = (M.op (σ (M.op x (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq301811
  have eq1195660 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq302131 eq1214
    | exact resolve eq1214 eq302131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214 eq302131
  have eq1196109 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1195660
       have i₂ := eq76 (M.op x sF0)
       grind)
    | exact superpose eq76 eq1195660
    | exact resolve eq1195660 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195660
  have eq1196194 : (M.op (σ x) (σ y)) = (σ (M.op (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) (M.op (M.op x (M.op x y)) (M.op x (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1196109
       have i₂ := eq76 (M.op (M.op x sF0) (M.op x sF0))
       grind)
    | exact superpose eq76 eq1196109
    | exact resolve eq1196109 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1196109
  have eq1196229 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op (M.op x (M.op x y)) (M.op x (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1593 eq1196194
    | exact resolve eq1196194 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593 eq1196194
  have eq1196240 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15388 eq1196229
    | exact resolve eq1196229 eq15388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15388 eq1196229
  have eq1197229 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq138266 eq1196240
    | exact resolve eq1196240 eq138266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138266 eq1196240
  have eq1197379 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1197229
  have eq1197408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq1197379
    | exact resolve eq1197379 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197379
  have eq1197414 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1197408
       have r₂ := eq28
       grind)
    | exact resolve eq1197408 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197408
  have eq1197425 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1197414 eq30
    | exact resolve eq30 eq1197414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1197414
  have eq1197678 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1197425
    | exact resolve eq1197425 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1197425
  have eq1197679 : x = y := by grind
  clear eq1197678
  have eq1197709 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1197679
       grind)
    | exact superpose eq1197679 eq19
    | exact resolve eq19 eq1197679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1197710 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1197679
       grind)
    | exact superpose eq1197679 eq25
    | exact resolve eq25 eq1197679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1197679
  have eq1198126 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1197710
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1197710
    | exact resolve eq1197710 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1197710
  have eq1198170 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1198126 eq27
    | exact resolve eq27 eq1198126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1198126
  have eq1199235 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1198170 eq74
    | exact resolve eq74 eq1198170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1198170
  have eq1199863 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1199235
       have i₂ := eq1197709
       grind)
    | exact superpose eq1197709 eq1199235
    | exact resolve eq1199235 eq1197709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197709 eq1199235
  have eq1199984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1199863 eq15
    | exact resolve eq15 eq1199863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199863
  have eq1200459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1199984
    | exact resolve eq1199984 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1199984
  have eq1200598 : False := by grind
  exact eq1200598

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_x_pyy_pxy_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) X3))) = (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 (M.op (M.op X5 (M.op X1 X2)) X3) X2 X1 X4
       have i₂ := eq62 X3 (M.op X1 X2) X5 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq62 X2 X0 X1 x
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq62 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 X1 X2 (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0))
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq79 X2 X1 (M.op (M.op X4 (M.op X1 X2)) X3)
       have i₂ := eq62 X3 (M.op X1 X2) X4 X0
       grind)
    | exact superpose eq62 eq79
    | exact resolve eq79 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq79 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq79 eq79
    | exact resolve eq79 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X2 (M.op (M.op X3 X2) X0)) X2 X4 X1
       have i₂ := eq79 X2 X3 X0
       grind)
    | exact superpose eq79 eq62
    | exact resolve eq62 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq101 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X3 X2) X0) X2 x
       grind)
    | exact superpose eq9 eq101
    | exact resolve eq101 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq112 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 (M.op X2 (M.op X2 X3)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq94 x X1 X2 X3 X4
       have i₂ := eq93 X3 X2 X1 x
       grind)
    | exact superpose eq93 eq94
    | exact resolve eq94 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq115 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) X3))) = (M.op X2 (M.op X2 (M.op X2 X3))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq76 x X1 X2 X3 X4 X5
       have i₂ := eq93 X3 X2 X1 x
       grind)
    | exact superpose eq93 eq76
    | exact resolve eq76 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq149 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X4 (M.op X2 (M.op X2 X0))) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq62 X3 (M.op X2 (M.op X2 X0)) X4 (M.op x X2)
       have i₂ := eq83 x X2 X0
       grind)
    | exact superpose eq83 eq62
    | exact resolve eq62 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq149 X0 X2 X3 x
       have i₂ := eq95 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq95 eq149
    | exact resolve eq149 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq149
  have eq233 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) = (M.op (M.op X5 (M.op X3 X1)) (M.op (M.op X3 X1) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 X4 (M.op X3 X1) X2 X5
       have i₂ := eq104 (M.op (M.op X2 (M.op X3 X1)) X4) X3 X1 X0
       grind)
    | (have i₁ := eq62 X4 (M.op X3 X1) X2 X5
       have i₂ := eq104 (M.op (M.op X2 (M.op X3 X1)) X4) X0 X1 X3
       grind)
    | exact superpose eq104 eq62
    | exact resolve eq62 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X1 X4)) = (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X1)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq233 X0 X1 X2 X3 X4 x
       have i₂ := eq93 X4 X1 X3 x
       grind)
    | exact superpose eq93 eq233
    | exact resolve eq233 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq233
  have eq397 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq397 (σ X0)
       grind)
    | exact superpose eq397 eq15
    | (have j1 := eq397 (σ X0)
       grind)
    | exact resolve eq15 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1557 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1649 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1557 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq1650 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq1917 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq104 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))) X5 X3 X2
       have i₂ := eq112 X1 (M.op X2 X3) X4 X0
       grind)
    | exact superpose eq112 eq104
    | exact resolve eq104 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1928 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1917 X0 X1 X2 X3 X4 X5
       have i₂ := eq151 X3 X2 (M.op (M.op X2 X3) X4)
       grind)
    | exact superpose eq151 eq1917
    | exact resolve eq1917 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq1917
  have eq2053 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op X3 (M.op X3 (M.op X3 (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1928 X0 X1 X2 X3 X4 x
       have i₂ := eq115 X2 X3 (M.op (M.op X2 X3) X4) x X2
       grind)
    | exact superpose eq115 eq1928
    | exact resolve eq1928 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1928
  have eq2122 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2053 X0 X1 X2 X3 X4
       have i₂ := eq79 X3 X2 X4
       grind)
    | exact superpose eq79 eq2053
    | exact resolve eq2053 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053
  have eq6614 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1650 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq6617 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6614 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq6614 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq6614 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq6614 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq6614 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq6675 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq6617 (τ X0) (τ X1)
       grind)
    | exact superpose eq6617 eq31
    | (have j1 := eq6617 (τ X0) (τ X1)
       grind)
    | exact resolve eq31 eq6617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7980 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq6675 X1 X0
       grind)
    | exact superpose eq6675 eq12
    | (have j0 := eq12 (τ X1) (τ X0)
       have j1 := eq6675 X1 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq6675 X0 X1
       grind)
    | exact resolve eq12 eq6675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8027 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) (τ X0)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7980 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7980
  have eq8035 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8027 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq8027
    | (have j0 := eq8027 X0 X1
       grind)
    | exact resolve eq8027 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8027
  have eq8048 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8035 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8035
    | exact resolve eq8035 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8067 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6675 X1 X0
       have i₂ := eq8035 X1 X0
       grind)
    | exact superpose eq8035 eq6675
    | (have j0 := eq6675 X1 X0
       have j1 := eq8035 X0 X1
       grind)
    | exact resolve eq6675 eq8035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8035
  have eq8127 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8067 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8067
  have eq8134 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8048 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq8048
    | (have j0 := eq8048 X0 X1
       grind)
    | exact resolve eq8048 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8048
  have eq8136 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8134 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq8134
    | (have j0 := eq8134 X0 X1
       grind)
    | exact resolve eq8134 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8134
  have eq8152 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq8136 X0 X1
       grind)
    | exact superpose eq8136 eq18
    | (have j1 := eq8136 X0 X1
       grind)
    | exact resolve eq18 eq8136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq8136
  have eq9181 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq404 (τ X0)
       have i₂ := eq8152 (τ X0) X0
       grind)
    | exact superpose eq8152 eq404
    | (have j0 := eq404 (τ X0)
       have j1 := eq8152 (τ X0) X0
       grind)
    | exact resolve eq404 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq9196 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq8152 (τ X0) X1
       grind)
    | exact superpose eq8152 eq17
    | (have j1 := eq8152 (τ X0) X1
       grind)
    | exact resolve eq17 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq8152
  have eq9202 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq9181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9181
  have eq9211 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9196 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9196
    | (have j0 := eq9196 X0 X1
       grind)
    | exact resolve eq9196 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9196
  have eq9219 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9202 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9202
    | (have j0 := eq9202 X0
       grind)
    | exact resolve eq9202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9202
  have eq9228 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9211 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9211
    | (have j0 := eq9211 X0 X1
       grind)
    | exact resolve eq9211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9211
  have eq9234 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9219 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9219
    | (have j0 := eq9219 X0
       grind)
    | exact resolve eq9219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9219
  have eq9238 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9228 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9228
    | (have j0 := eq9228 X0 X1
       grind)
    | exact resolve eq9228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9228
  have eq9305 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq9234 X0
       grind)
    | exact superpose eq9234 eq10
    | (have j1 := eq9234 X0
       grind)
    | exact resolve eq10 eq9234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9234
  have eq9334 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9238 X0 X1
       have i₂ := eq6675 X1 X0
       grind)
    | exact superpose eq6675 eq9238
    | (have j0 := eq9238 X0 X1
       have j1 := eq6675 X1 X0
       grind)
    | exact resolve eq9238 eq6675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6675 eq9238
  have eq9355 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9334 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9334
    | (have j0 := eq9334 X0 X1
       grind)
    | exact resolve eq9334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9334
  have eq9356 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9355 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9355
  have eq9387 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (M.op X1 (τ X0)) (τ (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq9305 X0
       grind)
    | exact superpose eq9305 eq9
    | (have j1 := eq9305 X0
       grind)
    | exact resolve eq9 eq9305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9305
  have eq9551 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9356 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9356
    | (have j0 := eq9356 X1 (σ X0)
       grind)
    | exact resolve eq9356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9591 : ∀ X0 X1 X2 : G, (τ X1) = (M.op (τ X0) (M.op (M.op X2 (τ X0)) (τ (k X0 X1)))) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X1) (τ X0) X2
       have i₂ := eq9356 X1 X0
       grind)
    | exact superpose eq9356 eq9
    | (have j1 := eq9356 X1 X0
       grind)
    | exact resolve eq9 eq9356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9356
  have eq9650 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9551 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9551
    | (have j0 := eq9551 X0 X1
       grind)
    | exact resolve eq9551 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9551
  have eq10024 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9650 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9650
    | (have j0 := eq9650 X1 (σ X0)
       grind)
    | exact resolve eq9650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9650
  have eq10088 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10024 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10024
    | (have j0 := eq10024 X0 X1
       grind)
    | exact resolve eq10024 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10024
  have eq10179 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq10088 X0 X1
       grind)
    | exact superpose eq10088 eq10
    | (have j1 := eq10088 X0 X1
       grind)
    | exact resolve eq10 eq10088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10088
  have eq10199 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10179 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10179
    | (have j0 := eq10179 X0 X1
       grind)
    | exact resolve eq10179 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10179
  have eq10268 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq10199 (σ X0) X1
       grind)
    | exact superpose eq10199 eq28
    | (have j1 := eq10199 (σ X0) X1
       grind)
    | exact resolve eq28 eq10199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10336 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10268 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10268
    | (have j0 := eq10268 X0 X1
       grind)
    | exact resolve eq10268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10268
  have eq10634 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10336 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10336
    | (have j0 := eq10336 X1 (σ X0)
       grind)
    | exact resolve eq10336 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10336
  have eq10717 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10634 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10634
    | (have j0 := eq10634 X0 X1
       grind)
    | exact resolve eq10634 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10634
  have eq10952 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10717 X0 X0
       have i₂ := eq397 X0
       grind)
    | exact superpose eq397 eq10717
    | (have j1 := eq397 X0
       grind)
    | exact resolve eq10717 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq10959 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10717 X0 X1
       have i₂ := eq10199 X1 X0
       grind)
    | exact superpose eq10199 eq10717
    | (have j0 := eq10717 X0 X1
       have j1 := eq10199 X1 X0
       grind)
    | exact resolve eq10717 eq10199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10199 eq10717
  have eq11027 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq10959 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10959
  have eq11028 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10952 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10952
  have eq11295 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11027 x y
       grind)
    | exact superpose eq11027 eq16
    | (have j1 := eq11027 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq11027 x y
       grind)
    | exact resolve eq16 eq11027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11027
  have eq11371 : y = (k y x) := by grind
  clear eq11295
  have eq11392 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6617 y x
       have i₂ := eq11371
       grind)
    | exact superpose eq11371 eq6617
    | (have j0 := eq6617 x y
       grind)
    | exact resolve eq6617 eq11371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6617 eq11371
  have eq11424 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79 x y X0
       have i₂ := eq11392
       grind)
    | exact superpose eq11392 eq79
    | exact resolve eq79 eq11392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11425 : ∀ X0 : G, (M.op y (M.op x (M.op x X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq83 y x X0
       have i₂ := eq11392
       grind)
    | exact superpose eq11392 eq83
    | exact resolve eq83 eq11392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11426 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq83 X0 y x
       have i₂ := eq11392
       grind)
    | exact superpose eq11392 eq83
    | exact resolve eq83 eq11392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11428 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X1 X0 x y
       have i₂ := eq11392
       grind)
    | exact superpose eq11392 eq104
    | exact resolve eq104 eq11392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq12142 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11424 x
       have i₂ := eq11392
       grind)
    | exact superpose eq11392 eq11424
    | exact resolve eq11424 eq11392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11392 eq11424
  have eq12214 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq12142
  have eq12475 : (M.op x y) = (M.op y (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11425 (M.op x y)
       have i₂ := eq12214
       grind)
    | exact superpose eq12214 eq11425
    | exact resolve eq11425 eq12214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12214
  have eq12555 : (M.op x y) = (M.op y (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq12475
  have eq12970 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 x) (M.op x x)) ∨ (M.op y X1) = (M.op (M.op X2 x) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 X0 x y
       have i₂ := eq11428 X2 X1
       grind)
    | exact superpose eq11428 eq83
    | (have j1 := eq11428 X2 X1
       grind)
    | exact resolve eq83 eq11428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11428
  have eq13750 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq11028 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11028
    | (have j0 := eq11028 (τ X0)
       grind)
    | exact resolve eq11028 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11028
  have eq34658 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq8127 X1 X0
       grind)
    | exact superpose eq8127 eq12
    | (have j0 := eq12 (τ X1) (τ X0)
       have j1 := eq8127 X1 X0
       grind)
    | exact resolve eq12 eq8127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8127
  have eq34734 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34658 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq34658
    | (have j0 := eq34658 X0 X1
       grind)
    | exact resolve eq34658 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34658
  have eq34735 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34734 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34734
  have eq34818 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X1)) = (τ (k (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34735 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34735
    | (have j0 := eq34735 (σ X0) (σ X1)
       grind)
    | exact resolve eq34735 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34735
  have eq34938 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X1)) = (τ (k (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34818 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq34818
    | (have j0 := eq34818 X0 X1
       grind)
    | exact resolve eq34818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34818
  have eq34949 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X1)) = (τ (k (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34938 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34938
    | (have j0 := eq34938 X0 X1
       grind)
    | exact resolve eq34938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34938
  have eq34958 : ∀ X0 X1 : G, (τ (σ X1)) = (k (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34949 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq34949
    | (have j0 := eq34949 X0 X1
       grind)
    | exact resolve eq34949 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34949
  have eq34961 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34958 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34958
    | (have j0 := eq34958 X0 X1
       grind)
    | exact resolve eq34958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34958
  have eq147488 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq13750 X0
       grind)
    | exact superpose eq13750 eq10
    | (have j1 := eq13750 X0
       grind)
    | exact resolve eq10 eq13750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13750
  have eq152063 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq147488 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147488
    | exact resolve eq147488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147488
  have eq271280 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (τ (k (σ X0) (σ X0))))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9387 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9387
    | (have j0 := eq9387 (σ X0) X1
       grind)
    | exact resolve eq9387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9387
  have eq271354 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (k (τ (σ X0)) X0))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq271280 X0 X1
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq271280
    | (have j0 := eq271280 X0 X1
       grind)
    | exact resolve eq271280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq271280
  have eq271355 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (k X0 X0))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq271354 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq271354
    | (have j0 := eq271354 X0 X1
       grind)
    | exact resolve eq271354 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271354
  have eq271396 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (k X0 X0))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (k X0 X0) X0 x X1
       have i₂ := eq271355 X0 x
       grind)
    | exact superpose eq271355 eq62
    | (have j1 := eq271355 X0 X1
       grind)
    | exact resolve eq62 eq271355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271355
  have eq271479 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79 X0 x (M.op X0 (k X0 X0))
       have i₂ := eq271396 X0 x
       grind)
    | exact superpose eq271396 eq79
    | (have j1 := eq271396 X0 x
       grind)
    | exact resolve eq79 eq271396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271396
  have eq271589 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq152063 X0
       have i₂ := eq271479 X0
       grind)
    | exact superpose eq271479 eq152063
    | (have j0 := eq152063 X0
       have j1 := eq271479 X0
       grind)
    | exact resolve eq152063 eq271479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152063 eq271479
  have eq271645 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq271589 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq271589
    | (have j0 := eq271589 X0
       grind)
    | exact resolve eq271589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271589
  have eq271646 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq271645 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271645
  have eq271986 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op (M.op X2 X0) (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (k X0 X0) X0 X2 X1
       have i₂ := eq271646 X0
       grind)
    | exact superpose eq271646 eq62
    | (have j1 := eq271646 X0
       grind)
    | exact resolve eq62 eq271646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271646
  have eq272024 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq271986 X0 x X2
       have i₂ := eq83 x X0 X0
       grind)
    | exact superpose eq83 eq271986
    | (have j0 := eq271986 X0 x X2
       grind)
    | exact resolve eq271986 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271986
  have eq272985 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op (M.op X2 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) (k X0 X0)) X0 X1
       have i₂ := eq272024 X0 X2
       grind)
    | exact superpose eq272024 eq9
    | (have j1 := eq272024 X0 X2
       grind)
    | exact resolve eq9 eq272024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272024
  have eq277124 : ∀ X0 X1 X2 : G, (τ X1) = (M.op (τ (σ X0)) (M.op (M.op X2 (τ (σ X0))) (k X0 (τ X1)))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9591 (σ X0) X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9591
    | (have j0 := eq9591 (σ X0) X1 X2
       grind)
    | exact resolve eq9591 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9591
  have eq277144 : ∀ X0 X1 X2 : G, (τ X1) = (M.op X0 (M.op (M.op X2 X0) (k X0 (τ X1)))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq277124 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277124
    | (have j0 := eq277124 X0 X1 X2
       grind)
    | exact resolve eq277124 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277124
  have eq277161 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X1 X0))) = X0 ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq277144 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277144
    | (have j0 := eq277144 X1 (σ X0) X2
       grind)
    | exact resolve eq277144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277144
  have eq277204 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X1 X0))) = X0 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq277161 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq277161
    | (have j0 := eq277161 X0 X1 X2
       grind)
    | exact resolve eq277161 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277161
  have eq277253 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (k X2 X0))) = X0 ∨ (σ X0) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (k X2 X0) X2 x X1
       have i₂ := eq277204 X0 X2 x
       grind)
    | exact superpose eq277204 eq62
    | (have j1 := eq277204 X0 X2 X2
       grind)
    | exact resolve eq62 eq277204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277204
  have eq277346 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 x (M.op X1 (k X1 X0))
       have i₂ := eq277253 X0 x X1
       grind)
    | exact superpose eq277253 eq79
    | (have j1 := eq277253 X0 X1 X1
       grind)
    | exact resolve eq79 eq277253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277253
  have eq277439 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X1 (M.op X1 X0)) = (M.op X1 (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq277346 X0 X1
       grind)
    | exact superpose eq277346 eq10
    | (have j1 := eq277346 X0 X1
       grind)
    | exact resolve eq10 eq277346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277346
  have eq277450 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq277439 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277439
    | (have j0 := eq277439 X0 X1
       grind)
    | exact resolve eq277439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277439
  have eq277471 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = (M.op X0 (M.op (M.op X3 X0) (k X0 X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (k X0 X1) X0 X3 X2
       have i₂ := eq277450 X1 X0
       grind)
    | exact superpose eq277450 eq62
    | (have j1 := eq277450 X1 X0
       grind)
    | exact resolve eq62 eq277450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277450
  have eq277497 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X3 X0) (k X0 X1))) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq277471 X0 X1 x X3
       have i₂ := eq83 x X0 X1
       grind)
    | exact superpose eq83 eq277471
    | (have j0 := eq277471 X0 X1 x X3
       grind)
    | exact resolve eq277471 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277471
  have eq277694 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (k (M.op X2 X1) X0))) = X0 ∨ (k X0 (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq237 X2 X1 x X2 (k (M.op X2 X1) X0)
       have i₂ := eq277497 (M.op X2 X1) X0 x
       grind)
    | exact superpose eq277497 eq237
    | (have j1 := eq277497 (M.op X2 X1) X0 x
       grind)
    | exact resolve eq237 eq277497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq277497
  have eq279342 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (k (M.op X3 X2) X0) ∨ (k X0 (M.op X3 X2)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq83 X1 X2 (k (M.op X3 X2) X0)
       have i₂ := eq277694 X0 X2 X3
       grind)
    | exact superpose eq277694 eq83
    | (have j1 := eq277694 X0 X2 X3
       grind)
    | exact resolve eq83 eq277694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277694
  have eq280274 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op (M.op X3 X2) X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34961 X0 (M.op X1 X2)
       have i₂ := eq279342 X0 X3 X2 X1
       grind)
    | exact superpose eq279342 eq34961
    | (have j0 := eq34961 X0 (M.op X1 X2)
       have j1 := eq279342 X0 X3 X2 X1
       grind)
    | (have r₁ := eq34961 (M.op (M.op X1 X0) X0) X0
       have r₂ := eq279342 X0 X1 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq34961 X0 (M.op X3 X2)
       have r₂ := eq279342 X0 X1 X2 X3
       grind)
    | exact resolve eq34961 eq279342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34961 eq279342
  have eq280278 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (k (M.op X1 X2) X0) ∨ (M.op (M.op X3 X2) X0) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq280274 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280274
  have eq319001 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X3 X1) X2) ∨ (M.op (M.op X3 X1) X2) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq280278 X2 X0 X1 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280278
  have eq340426 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 (M.op X2 X0))) X4) ≠ X0 ∨ (M.op (M.op X3 (M.op X2 (M.op X2 X0))) X4) = (k X0 X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq319001 (M.op X0 x) (M.op x (M.op x X2)) X2 X3
       have i₂ := eq83 X0 x X2
       grind)
    | exact superpose eq83 eq319001
    | (have r₁ := eq319001 X0 x (M.op x (M.op x (M.op X0 x))) X0
       have r₂ := eq83 X0 x (M.op X0 x)
       grind)
    | exact resolve eq319001 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319001
  have eq340497 : ∀ X0 X2 X3 X4 : G, (M.op X0 X4) ≠ X0 ∨ (M.op (M.op X3 (M.op X2 (M.op X2 X0))) X4) = (k X0 X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq340426 X0 X2 X3 X4
       have i₂ := eq2122 X3 X2 X2 X0 X4
       grind)
    | exact superpose eq2122 eq340426
    | (have j0 := eq340426 X0 X2 X3 X4
       grind)
    | exact resolve eq340426 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340426
  have eq340498 : ∀ X0 X4 : G, (M.op X0 X4) ≠ X0 ∨ (M.op X0 X4) = (k X0 X4) := by
    intro X0 X4
    first
    | (have i₁ := eq340497 X0 x x X4
       have i₂ := eq2122 x x x X0 X4
       grind)
    | exact superpose eq2122 eq340497
    | (have j0 := eq340497 X0 x x X4
       grind)
    | (have r₁ := eq340497 (M.op x (M.op x (M.op x x))) x x (M.op x (M.op x x))
       have r₂ := eq2122 x x x x (M.op x (M.op x x))
       grind)
    | exact resolve eq340497 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122 eq340497
  have eq357157 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X1 X0) X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 x (k X0 X0)
       have i₂ := eq272985 X0 X1 x
       grind)
    | exact superpose eq272985 eq79
    | (have j1 := eq272985 X0 X1 x
       grind)
    | exact resolve eq79 eq272985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272985
  have eq357167 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq357157 X0 x
       have i₂ := eq79 X0 x X0
       grind)
    | exact superpose eq79 eq357157
    | (have j0 := eq357157 X0 x
       grind)
    | exact resolve eq357157 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357157
  have eq357172 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq357167 X0
       have j1 := eq340498 X0 X0
       grind)
    | (have r₁ := eq357167 x
       have r₂ := eq340498 x x
       grind)
    | exact resolve eq357167 eq340498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340498 eq357167
  have eq364981 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq357172 (σ X0)
       grind)
    | exact superpose eq357172 eq15
    | exact resolve eq15 eq357172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365034 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq357172 (τ X0)
       grind)
    | exact superpose eq357172 eq31
    | exact resolve eq31 eq357172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq365226 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365034 X0
       have i₂ := eq357172 X0
       grind)
    | exact superpose eq357172 eq365034
    | exact resolve eq365034 eq357172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365034
  have eq365261 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq364981 X0
       have i₂ := eq357172 X0
       grind)
    | exact superpose eq357172 eq364981
    | exact resolve eq364981 eq357172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357172 eq364981
  have eq368935 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq365226 X0
       grind)
    | exact superpose eq365226 eq9
    | exact resolve eq9 eq365226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369759 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq365261 X0
       grind)
    | exact superpose eq365261 eq9
    | exact resolve eq9 eq365261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378169 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq368935 X0 (τ X0)
       have i₂ := eq365226 X0
       grind)
    | exact superpose eq365226 eq368935
    | exact resolve eq368935 eq365226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368935
  have eq378254 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq378169 X0
       have i₂ := eq365226 (M.op X0 X0)
       grind)
    | exact superpose eq365226 eq378169
    | exact resolve eq378169 eq365226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365226 eq378169
  have eq378650 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq369759 X0 (σ X0)
       have i₂ := eq365261 X0
       grind)
    | exact superpose eq365261 eq369759
    | exact resolve eq369759 eq365261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369759
  have eq378736 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq378650 X0
       have i₂ := eq365261 (M.op X0 X0)
       grind)
    | exact superpose eq365261 eq378650
    | exact resolve eq378650 eq365261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365261 eq378650
  have eq379311 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq378254 X0
       have i₂ := eq62 X0 X0 X1 X0
       grind)
    | exact superpose eq62 eq378254
    | exact resolve eq378254 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378254
  have eq379903 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq378736 X0
       have i₂ := eq62 X0 X0 X1 X0
       grind)
    | exact superpose eq62 eq378736
    | exact resolve eq378736 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq379912 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op X1 x) X0) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq378736 x
       have i₂ := eq12970 x X0 X1
       grind)
    | exact superpose eq12970 eq378736
    | (have j1 := eq12970 X0 X0 X1
       grind)
    | exact resolve eq378736 eq12970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12970
  have eq379924 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq378736 y
       have i₂ := eq11426 y
       grind)
    | exact superpose eq11426 eq378736
    | exact resolve eq378736 eq11426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11426 eq378736
  have eq380299 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79 (σ x) (σ y) X0
       have i₂ := eq379924
       grind)
    | exact superpose eq379924 eq79
    | exact resolve eq79 eq379924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq380484 : ∀ X0 X1 : G, (M.op X0 (τ (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq379311 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq379311
    | exact resolve eq379311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379311
  have eq404412 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op y X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq379912 X1 X0
       grind)
    | exact superpose eq379912 eq16
    | (have j1 := eq379912 X1 X0
       grind)
    | exact resolve eq16 eq379912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404474 : (σ x) = (M.op (σ x) (σ (M.op x (M.op y x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq379903 x x
       have i₂ := eq379912 x x
       grind)
    | exact superpose eq379912 eq379903
    | exact resolve eq379903 eq379912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379903 eq379912
  have eq413316 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq380299 (σ x)
       have i₂ := eq379924
       grind)
    | exact superpose eq379924 eq380299
    | exact resolve eq380299 eq379924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379924 eq380299
  have eq413345 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq413316
  have eq413356 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq83 X0 (σ x) (σ y)
       have i₂ := eq413345
       grind)
    | exact superpose eq413345 eq83
    | exact resolve eq83 eq413345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq413345
  have eq413544 : x = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq380484 x x
       have i₂ := eq413356 x
       grind)
    | exact superpose eq413356 eq380484
    | exact resolve eq380484 eq413356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380484 eq413356
  have eq413751 : (M.op y (M.op x x)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11425 (τ (M.op (σ x) (σ y)))
       have i₂ := eq413544
       grind)
    | exact superpose eq413544 eq11425
    | exact resolve eq11425 eq413544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11425 eq413544
  have eq413780 : (M.op y (M.op x x)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq413751
  have eq421880 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq413780
       grind)
    | exact superpose eq413780 eq11
    | exact resolve eq11 eq413780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413780
  have eq422275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq421880
       have i₂ := eq12555
       grind)
    | exact superpose eq12555 eq421880
    | exact resolve eq421880 eq12555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12555 eq421880
  have eq422288 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq422275
  have eq422289 : x = (M.op x y) := by
    first
    | (have r₁ := eq422288
       have r₂ := eq16
       grind)
    | exact resolve eq422288 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422288
  have eq422290 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq422289
       grind)
    | exact superpose eq422289 eq16
    | exact resolve eq16 eq422289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425932 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op y X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq404412 X0 X1
       have i₂ := eq422289
       grind)
    | exact superpose eq422289 eq404412
    | (have j0 := eq404412 X0 X1
       grind)
    | exact resolve eq404412 eq422289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404412
  have eq426020 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have j0 := eq425932 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425932
  have eq429178 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq422289
       grind)
    | exact superpose eq422289 eq9
    | exact resolve eq9 eq422289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422289
  have eq429997 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq429178 x
       have i₂ := eq426020 x x
       grind)
    | exact superpose eq426020 eq429178
    | exact resolve eq429178 eq426020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426020 eq429178
  have eq430290 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq404474
       have i₂ := eq429997
       grind)
    | exact superpose eq429997 eq404474
    | exact resolve eq404474 eq429997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404474 eq429997
  have eq430385 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq430290
  have eq430946 : False := by grind
  exact eq430946

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
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
  have eq69 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X3 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) = (M.op X3 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X4 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)) X3 X2
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X0) X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq55 x X2 X0 X3
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq55 X1 (M.op X0 X2) X0 x
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X3 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)) X2
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X2 (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) X1
       have i₂ := eq73 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq73 eq73
    | exact resolve eq73 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1 X4
       have i₂ := eq73 X1 X0 X2
       grind)
    | exact superpose eq73 eq55
    | exact resolve eq55 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X2 X1) X0) X1 x
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq113 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op (M.op X2 X1) (M.op (M.op X4 (M.op X2 X1)) (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op X1 (M.op X1 X0)) (M.op X2 X1) X4
       have i₂ := eq77 X1 X2 X0
       grind)
    | exact superpose eq77 eq55
    | exact resolve eq55 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X4 (M.op X1 (M.op X1 X0))) X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq55 (M.op x X1) X3 (M.op X1 (M.op X1 X0)) X4
       have i₂ := eq77 X1 x X0
       grind)
    | exact superpose eq77 eq55
    | exact resolve eq55 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X3))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq73 (M.op X1 (M.op X1 X0)) X3 (M.op x X1)
       have i₂ := eq77 X1 x X0
       grind)
    | exact superpose eq77 eq73
    | exact resolve eq73 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq118 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq114 X0 X1 X3 x
       have i₂ := eq88 X3 X1 (M.op X1 X0) x
       grind)
    | exact superpose eq88 eq114
    | exact resolve eq114 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq119 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X1 (M.op X1 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X0 X1 X2 X3 x
       have i₂ := eq88 (M.op X1 (M.op X1 X0)) X2 X1 x
       grind)
    | exact superpose eq88 eq113
    | exact resolve eq113 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq113
  have eq184 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op (M.op X1 (M.op X2 X3)) X4)) = (M.op (M.op X5 (M.op X2 X3)) (M.op (M.op X2 X3) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X5 X4 (M.op X2 X3) X1
       have i₂ := eq96 (M.op (M.op X1 (M.op X2 X3)) X4) X3 X2 X0
       grind)
    | (have i₁ := eq55 X5 X4 (M.op X2 X3) X1
       have i₂ := eq96 (M.op (M.op X1 (M.op X2 X3)) X4) X3 X0 X2
       grind)
    | exact superpose eq96 eq55
    | exact resolve eq55 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq186 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 X2)) (M.op (M.op X0 X2) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq77 (M.op X1 X2) X4 X3
       have i₂ := eq96 (M.op (M.op X1 X2) X3) X2 X1 X0
       grind)
    | (have i₁ := eq77 (M.op X1 X2) X4 X3
       have i₂ := eq96 (M.op (M.op X1 X2) X3) X2 X0 X1
       grind)
    | exact superpose eq96 eq77
    | exact resolve eq77 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X3) (M.op (M.op X1 (M.op X2 X3)) X4)) = (M.op X3 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq184 X0 X1 X2 X3 X4 x
       have i₂ := eq86 x X4 X2 X3
       grind)
    | exact superpose eq86 eq184
    | exact resolve eq184 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq184
  have eq1141 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq1199 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq1213 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1216 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1213 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1213
    | (have j0 := eq1213 (σ X0) (σ X1)
       grind)
    | exact resolve eq1213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op (τ X1) X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1213 X0 (τ X1)
       grind)
    | exact superpose eq1213 eq19
    | (have j1 := eq1213 X0 (τ X1)
       grind)
    | exact resolve eq19 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq1213 (σ X0) X1
       grind)
    | exact superpose eq1213 eq28
    | (have j1 := eq1213 (σ X0) X1
       grind)
    | exact resolve eq28 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1213
  have eq1751 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 (M.op X0 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq116 X1 X0 X2
       have i₂ := eq96 (M.op X1 X2) (M.op X0 X1) X0 X3
       grind)
    | (have i₁ := eq116 X1 X0 X2
       have i₂ := eq96 (M.op X1 X2) (M.op X0 X1) X3 X0
       grind)
    | exact superpose eq96 eq116
    | exact resolve eq116 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq2021 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) X1) = (M.op (M.op X5 (M.op X4 X2)) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq119 X1 X2 X0 X3
       have i₂ := eq119 X1 X2 X4 X5
       grind)
    | exact superpose eq119 eq119
    | exact resolve eq119 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2098 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq96 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1))) X3 X5 X2
       have i₂ := eq119 X1 (M.op X2 X3) X0 X4
       grind)
    | exact superpose eq119 eq96
    | exact resolve eq96 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq119
  have eq2107 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2098 X0 X1 X2 X3 X4 X5
       have i₂ := eq118 X3 X2 (M.op (M.op X2 X3) X1)
       grind)
    | exact superpose eq118 eq2098
    | exact resolve eq2098 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq2098
  have eq2228 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2107 X0 X1 X2 X3 X4 x
       have i₂ := eq69 X2 X1 X2 X3 x
       grind)
    | exact superpose eq69 eq2107
    | exact resolve eq2107 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2107
  have eq3621 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X3) (M.op (M.op X4 X3) X2)) = (M.op (M.op X5 (M.op X0 (M.op X4 X3))) (M.op (M.op X0 (M.op X4 X3)) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq77 (M.op X0 (M.op X4 X3)) X5 (M.op (M.op X1 X3) (M.op (M.op X4 X3) X2))
       have i₂ := eq186 X1 X4 X3 X2 X0
       grind)
    | exact superpose eq186 eq77
    | exact resolve eq77 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq3633 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X3) (M.op (M.op X4 X3) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X3)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3621 X0 X1 X2 X3 X4 x
       have i₂ := eq2228 X0 (M.op (M.op X0 (M.op X4 X3)) X2) X4 X3 x
       grind)
    | exact superpose eq2228 eq3621
    | exact resolve eq3621 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621
  have eq3881 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    grind
  have eq3882 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3881 X0 X1 X2
       have i₂ := eq77 X0 (M.op X1 (M.op X2 X0)) X0
       grind)
    | exact superpose eq77 eq3881
    | exact resolve eq3881 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3881
  have eq4015 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (k (M.op (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X4 (M.op X3 (M.op (M.op X1 (M.op X2 X0)) X0))) (M.op (M.op X1 (M.op X2 X0)) X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3882 (M.op (M.op X1 (M.op X2 X0)) X0) X4 X3
       have i₂ := eq189 (M.op X1 (M.op X2 X0)) X1 X2 X0 X0
       grind)
    | exact superpose eq189 eq3882
    | exact resolve eq3882 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq3882
  have eq4115 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (k (M.op (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4015 X0 X1 X2 x x
       have i₂ := eq2228 x (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X1 (M.op X2 X0)) X0 x
       grind)
    | exact superpose eq2228 eq4015
    | exact resolve eq4015 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4015
  have eq4145 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (k X0 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4115 X0 X1 X2
       have i₂ := eq77 X0 (M.op X1 (M.op X2 X0)) X0
       grind)
    | exact superpose eq77 eq4115
    | exact resolve eq4115 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115
  have eq5255 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X5 X3)) (M.op (M.op X1 (M.op X0 X3)) (M.op X3 X2))) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2021 X5 (M.op (M.op X1 (M.op X0 X3)) (M.op X3 X2)) X3 X4 X0 X0
       have i₂ := eq1751 X0 X3 X2 X1
       grind)
    | exact superpose eq1751 eq2021
    | exact resolve eq2021 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751 eq2021
  have eq9545 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq1141 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq1141 X0 X1
       grind)
    | exact superpose eq1141 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq1141 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq1141 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq1141 X0 X1
       grind)
    | exact resolve eq13 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq9651 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9545 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9545
  have eq9652 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9651 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9651
  have eq9658 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9652 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9652
    | (have j0 := eq9652 X0 X1
       grind)
    | exact resolve eq9652 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9652
  have eq9665 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1227 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1227
    | exact resolve eq1227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq9718 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9665 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9665
    | (have j0 := eq9665 X0 X1
       grind)
    | exact resolve eq9665 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9665
  have eq22177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) X2) = (k X2 (M.op (M.op X3 X2) (M.op (M.op X0 X2) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4145 X2 X1 X0
       have i₂ := eq3633 X1 X3 X2 X2 X0
       grind)
    | exact superpose eq3633 eq4145
    | exact resolve eq4145 eq3633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633 eq4145
  have eq24336 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op (σ X1) (σ X0)))) X4) = (M.op (σ X1) X4) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2228 X3 X4 (σ X0) (σ X1) X2
       have i₂ := eq1216 X0 X1
       grind)
    | (have i₁ := eq2228 X0 X1 (σ X1) (σ X0) X4
       have i₂ := eq1216 X0 X1
       grind)
    | exact superpose eq1216 eq2228
    | (have j1 := eq1216 X0 X1
       grind)
    | exact resolve eq2228 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq24389 : ∀ X0 X1 X4 : G, (M.op (σ X0) X4) = (M.op (σ X1) X4) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq24336 X0 X1 x x X4
       have i₂ := eq2228 x X4 (σ X1) (σ X0) x
       grind)
    | exact superpose eq2228 eq24336
    | (have j0 := eq24336 X0 X1 x x X4
       grind)
    | exact resolve eq24336 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228 eq24336
  have eq24448 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (σ X2) X1) ∨ (M.op X0 (σ X2)) = (σ (k X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24389 X0 (τ X0) x
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24389
    | exact resolve eq24389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24874 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq24389 y x X0
       grind)
    | exact superpose eq24389 eq16
    | (have j1 := eq24389 y x X0
       grind)
    | exact resolve eq16 eq24389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24964 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq24389 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24389
  have eq24979 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k (σ X2) X0) ∨ (M.op X0 X1) = (M.op (σ X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24448 X0 X1 X2
       have i₂ := eq19 X0 X2
       grind)
    | exact superpose eq19 eq24448
    | (have j0 := eq24448 X0 X1 X2
       grind)
    | exact resolve eq24448 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24448
  have eq24985 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X2) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24979 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24979
    | exact resolve eq24979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24979
  have eq26859 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) X1) = (M.op (σ x) X1) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24874 X1
       have i₂ := eq24985 y x X0
       grind)
    | exact superpose eq24985 eq24874
    | (have j0 := eq24874 X1
       have j1 := eq24985 (σ y) (σ x) X1
       grind)
    | exact resolve eq24874 eq24985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24985
  have eq26862 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq24874 X0
       have i₂ := eq9718 x y
       grind)
    | exact superpose eq9718 eq24874
    | (have j0 := eq24874 X0
       have j1 := eq9718 y x
       grind)
    | (have r₁ := eq24874 X0
       have r₂ := eq9718 x y
       grind)
    | exact resolve eq24874 eq9718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9718
  have eq26863 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq26862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26862
  have eq26866 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (σ x) X1) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have j0 := eq26859 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26859
  have eq78837 : ∀ X0 X1 X3 X4 : G, (M.op (k X0 (M.op (M.op X3 X0) (M.op (M.op X1 X0) X0))) (M.op X0 (M.op X0 X4))) = X4 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq77 X0 (M.op x (M.op X1 X0)) X4
       have i₂ := eq22177 X1 x X0 X3
       grind)
    | exact superpose eq22177 eq77
    | exact resolve eq77 eq22177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq22177
  have eq139968 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) ≠ (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24964 (τ X0) (τ X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq24964
    | exact resolve eq24964 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24964
  have eq140075 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X1 X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq139968 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq139968
    | (have j0 := eq139968 X0 X1
       grind)
    | exact resolve eq139968 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139968
  have eq140097 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X1 X0) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq140075 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq140075
    | (have j0 := eq140075 X0 X1
       grind)
    | exact resolve eq140075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140075
  have eq140114 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140097 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq140097
    | (have j0 := eq140097 X0 X1
       grind)
    | exact resolve eq140097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140097
  have eq140127 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X1 X0))) ∨ (M.op X1 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140114 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140114
    | (have j0 := eq140114 X0 X1
       grind)
    | exact resolve eq140114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140114
  have eq140136 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140127 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq140127
    | (have j0 := eq140127 X0 X1
       grind)
    | exact resolve eq140127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140127
  have eq140533 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9658 (τ X1) (τ X0)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9658
    | (have j0 := eq9658 (τ (k X1 X0)) (τ X1)
       grind)
    | exact resolve eq9658 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9658
  have eq141926 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X1 X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq140533 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140533
    | (have j0 := eq140533 X0 X1
       grind)
    | exact resolve eq140533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140533
  have eq141955 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq141926 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq141926
    | (have j0 := eq141926 X0 X1
       grind)
    | exact resolve eq141926 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141926
  have eq141979 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq141955 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141955
    | (have j0 := eq141955 X0 X1
       grind)
    | exact resolve eq141955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141955
  have eq142000 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq141979 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq141979
    | (have j0 := eq141979 X0 X1
       grind)
    | exact resolve eq141979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141979
  have eq142017 : ∀ X0 X1 : G, (σ (τ (k X1 X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq142000 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq142000
    | (have j0 := eq142000 X0 X1
       grind)
    | exact resolve eq142000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142000
  have eq142030 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X1 X0))) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq142017 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq142017
    | (have j0 := eq142017 X0 X1
       grind)
    | exact resolve eq142017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142017
  have eq142039 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq142030 X0 X1
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq142030
    | (have j0 := eq142030 X0 X1
       grind)
    | exact resolve eq142030 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142030
  have eq142347 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq142039
  have eq143489 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq142347 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142347
  have eq143804 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq143489 (τ X0) X1
       grind)
    | exact superpose eq143489 eq19
    | (have j1 := eq143489 (τ X0) X1
       grind)
    | exact resolve eq19 eq143489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq144502 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq143489 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143489
  have eq144790 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq144502 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144502
  have eq144880 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq144790 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq144790
    | exact resolve eq144790 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144911 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq144880 X0
       have i₂ := eq144790 X0
       grind)
    | exact superpose eq144790 eq144880
    | exact resolve eq144880 eq144790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144790 eq144880
  have eq145336 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq26866 X0 (σ y)
       have i₂ := eq144911 y
       grind)
    | exact superpose eq144911 eq26866
    | (have j0 := eq26866 X0 x
       grind)
    | exact resolve eq26866 eq144911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26866
  have eq145337 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq26863 (σ y)
       have i₂ := eq144911 y
       grind)
    | exact superpose eq144911 eq26863
    | exact resolve eq26863 eq144911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26863
  have eq145458 : ∀ X0 X1 X2 X3 X4 : G, (σ X0) = (M.op (M.op X2 (M.op X1 (σ X0))) (M.op (M.op X4 (M.op X3 (σ X0))) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5255 X3 X4 (σ X0) (σ X0) X2 X1
       have i₂ := eq144911 X0
       grind)
    | exact superpose eq144911 eq5255
    | exact resolve eq5255 eq144911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239099 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq145336 X0
       grind)
    | exact superpose eq145336 eq16
    | (have j1 := eq145336 X0
       grind)
    | exact resolve eq16 eq145336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145336
  have eq240020 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145337
       grind)
    | exact superpose eq145337 eq16
    | exact resolve eq16 eq145337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145337
  have eq512839 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq143804 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq143804
    | exact resolve eq143804 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143804
  have eq514278 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq512839 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq512839
    | (have j0 := eq512839 X0 X1
       grind)
    | exact resolve eq512839 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512839
  have eq514639 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (k y x) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq24874 X0
       have i₂ := eq514278 x y
       grind)
    | exact superpose eq514278 eq24874
    | (have j0 := eq24874 X0
       have j1 := eq514278 x y
       grind)
    | (have r₁ := eq24874 X0
       have r₂ := eq514278 x y
       grind)
    | exact resolve eq24874 eq514278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24874 eq514278
  have eq515608 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (k y x) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq514639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514639
  have eq515868 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq515608 (σ y)
       have i₂ := eq144911 y
       grind)
    | exact superpose eq144911 eq515608
    | exact resolve eq515608 eq144911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515608
  have eq516827 : (τ (σ (M.op y y))) = (k y (τ (σ x))) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq1234 y (σ x)
       have i₂ := eq515868
       grind)
    | exact superpose eq515868 eq1234
    | exact resolve eq1234 eq515868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234 eq515868
  have eq517250 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq516827
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq516827
    | exact resolve eq516827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516827
  have eq517302 : (k y x) = (M.op y y) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq517250
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq517250
    | exact resolve eq517250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517250
  have eq517303 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) := by grind
  clear eq517302
  have eq517494 : ∀ X0 X1 X2 X3 : G, (σ x) = (M.op (M.op X1 (M.op X0 (σ y))) (M.op (M.op X3 (M.op X2 (σ y))) (σ (M.op y y)))) ∨ (k y x) = (M.op y y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5255 X2 X3 (σ x) (σ y) X1 X0
       have i₂ := eq517303
       grind)
    | exact superpose eq517303 eq5255
    | exact resolve eq5255 eq517303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5255 eq517303
  have eq517831 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq517494 x x x x
       have i₂ := eq145458 y x x x x
       grind)
    | exact superpose eq145458 eq517494
    | exact resolve eq517494 eq145458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145458 eq517494
  have eq519795 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq140136 x y
       have i₂ := eq517831
       grind)
    | exact superpose eq517831 eq140136
    | (have r₁ := eq140136 x y
       have r₂ := eq517831
       grind)
    | exact resolve eq140136 eq517831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140136 eq517831
  have eq519796 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq519795
  have eq519798 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq240020
       have i₂ := eq519796
       grind)
    | exact superpose eq519796 eq240020
    | exact resolve eq240020 eq519796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240020
  have eq519799 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y X0) = (M.op x X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq239099 X0
       have i₂ := eq519796
       grind)
    | exact superpose eq519796 eq239099
    | (have j0 := eq239099 X0
       grind)
    | exact resolve eq239099 eq519796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239099 eq519796
  have eq520270 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq519799 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519799
  have eq520271 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq519798
  have eq521323 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq520270 x
       have i₂ := eq520271
       grind)
    | exact superpose eq520271 eq520270
    | exact resolve eq520270 eq520271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520270 eq520271
  have eq521656 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq521323
  have eq521935 : ∀ X0 X1 : G, y = (M.op (k x (M.op (M.op X0 x) (M.op (M.op X1 x) x))) (M.op x (M.op x x))) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq78837 x X1 X0 y
       have i₂ := eq521656
       grind)
    | exact superpose eq521656 eq78837
    | exact resolve eq78837 eq521656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521656
  have eq522022 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq521935 x x
       have i₂ := eq78837 x x x x
       grind)
    | (have i₁ := eq521935 x x
       have i₂ := eq78837 x x x (M.op (k x (M.op (M.op x x) (M.op (M.op x x) x))) (M.op x (M.op x x)))
       grind)
    | exact superpose eq78837 eq521935
    | exact resolve eq521935 eq78837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78837 eq521935
  have eq522064 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq522022
       grind)
    | exact superpose eq522022 eq10
    | exact resolve eq10 eq522022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522022
  have eq522258 : x = y ∨ x = y := by
    first
    | (have i₁ := eq522064
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq522064
    | exact resolve eq522064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522064
  have eq522259 : x = y := by grind
  clear eq522258
  have eq522274 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq522259
       grind)
    | exact superpose eq522259 eq16
    | exact resolve eq16 eq522259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522259
  have eq522283 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq522274
       have i₂ := eq144911 x
       grind)
    | exact superpose eq144911 eq522274
    | (have r₁ := eq522274
       have r₂ := eq144911 x
       grind)
    | exact resolve eq522274 eq144911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144911 eq522274
  have eq522284 : False := by grind
  exact eq522284
