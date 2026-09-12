import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyy_pxx_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
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
  clear eq36
  have eq79 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq92 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq112 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq112 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq113 (σ X0)
       grind)
    | exact superpose eq113 eq10
    | exact resolve eq10 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq43
    | exact resolve eq43 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq117 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq76
    | exact resolve eq76 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq118 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq49
    | exact resolve eq49 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq119 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq118
    | exact resolve eq118 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq117
    | exact resolve eq117 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq116
    | exact resolve eq116 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq122 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq115
    | exact resolve eq115 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq103
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq103
    | exact resolve eq103 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq126
    | exact resolve eq126 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq113 sF1
       grind)
    | exact superpose eq113 eq137
    | exact resolve eq137 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq143 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq113 sF0
       grind)
    | exact superpose eq113 eq140
    | exact resolve eq140 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq165 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq143 eq16
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq308 eq50
    | exact resolve eq50 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op (M.op x y) (M.op x y)) y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq345 eq13
    | (have j0 := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq13 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq382 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq50 eq375
    | exact resolve eq375 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq375
  have eq424 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq113 (τ X0)
       grind)
    | exact superpose eq113 eq34
    | exact resolve eq34 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq435 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq424 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq424
    | exact resolve eq424 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq437 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq435 X0
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq435
    | exact resolve eq435 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq435
  have eq975 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq437 X0
       grind)
    | exact superpose eq437 eq16
    | exact resolve eq16 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq1239 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (τ X0) (τ X0) x
       have i₂ := eq975 X0
       grind)
    | exact superpose eq975 eq53
    | exact resolve eq53 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq975
  have eq5772 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq79
    | (have j0 := eq79 X0
       grind)
    | exact resolve eq79 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq122
  have eq5938 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5772 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5772
    | (have j0 := eq5772 y
       grind)
    | exact resolve eq5772 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5772
  have eq5962 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5938
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5938
    | exact resolve eq5938 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5938
  have eq5981 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5962
    | exact resolve eq5962 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5962
  have eq5989 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5981
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq5981
    | exact resolve eq5981 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq5981
  have eq5997 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5989
    | exact resolve eq5989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989
  have eq20241 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq52 X0 y y
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq52
    | exact resolve eq52 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22263 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq5997 eq127
    | exact resolve eq127 eq5997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq5997
  have eq22353 : (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq119 eq22263
    | exact resolve eq22263 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22263
  have eq24866 : y = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq308 y
       have i₂ := eq22353
       grind)
    | exact superpose eq22353 eq308
    | exact resolve eq308 eq22353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq22353
  have eq580325 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20241 y
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq20241
    | exact resolve eq20241 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq20241
  have eq580363 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq580325
  have eq580364 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq580363
       have i₂ := eq52 x x x
       grind)
    | (have i₁ := eq580363
       have i₂ := eq52 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq52 eq580363
    | exact resolve eq580363 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580363
  have eq580444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq580364 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq580364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq580444
    | exact resolve eq580444 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580444
  have eq580522 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq580445
       have r₂ := eq27
       grind)
    | exact resolve eq580445 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580445
  have eq580543 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq580522
    | exact resolve eq580522 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580522
  have eq580745 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq580543 eq52
    | exact resolve eq52 eq580543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581640 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq580543 eq580745
    | exact resolve eq580745 eq580543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580543 eq580745
  have eq581684 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq581640
  have eq581695 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq581684
       have i₂ := eq52 sF2 sF2 sF2
       grind)
    | (have i₁ := eq581684
       have i₂ := eq52 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq52 eq581684
    | exact resolve eq581684 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq581684
  have eq581697 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq581695 eq27
    | exact resolve eq27 eq581695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581699 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq581695 eq67
    | (have r₁ := eq67
       have r₂ := eq581695
       grind)
    | exact resolve eq67 eq581695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq581700 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq581695 eq253
    | exact resolve eq253 eq581695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq581755 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq581699
  have eq581765 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq581700 eq322
    | exact resolve eq322 eq581700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq581700
  have eq581804 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq581695 eq581765
    | exact resolve eq581765 eq581695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581695 eq581765
  have eq581836 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq581804
  have eq584543 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq581755 eq580364
    | exact resolve eq580364 eq581755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580364 eq581755
  have eq584546 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq584543
  have eq585109 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq584546 eq581836
    | exact resolve eq581836 eq584546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581836 eq584546
  have eq585261 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq585109
  have eq585296 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq585261
       have r₂ := eq581697
       grind)
    | exact resolve eq585261 eq581697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581697 eq585261
  have eq586672 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq585296 eq29
    | exact resolve eq29 eq585296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq585296
  have eq587653 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq586672
    | exact resolve eq586672 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586672
  have eq587654 : x = (M.op x y) ∨ x = y := by grind
  clear eq587653
  have eq587832 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq587654 eq20
    | exact resolve eq20 eq587654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587848 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq587654 eq143
    | exact resolve eq143 eq587654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq587880 : x = (M.op (M.op x x) x) ∨ x = y := by
    first
    | exact superpose eq587654 eq252
    | exact resolve eq252 eq587654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq589001 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq587848
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq587848
    | exact resolve eq587848 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587848
  have eq589014 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq587832
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq587832
    | exact resolve eq587832 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587832
  have eq591944 : x = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq320 (M.op x x)
       have i₂ := eq587880
       grind)
    | exact superpose eq587880 eq320
    | exact resolve eq320 eq587880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq587880
  have eq591979 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq587654 eq591944
    | exact resolve eq591944 eq587654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591944
  have eq592008 : x = (M.op x x) ∨ x = y := by grind
  clear eq591979
  have eq592009 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq121
       have i₂ := eq592008
       grind)
    | exact superpose eq592008 eq121
    | exact resolve eq121 eq592008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq592008
  have eq592396 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq592009
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq592009
    | exact resolve eq592009 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592009
  have eq595595 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq589001 eq592396
    | exact resolve eq592396 eq589001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589001 eq592396
  have eq595749 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq595595
  have eq595880 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq595749 eq165
    | exact resolve eq165 eq595749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq596010 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ (M.op x y))) (M.op (τ (σ x)) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq595749 eq1239
    | exact resolve eq1239 eq595749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq595749
  have eq596152 : ∀ X0 : G, x = (M.op (τ (σ (M.op x y))) (M.op x X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28 eq596010
    | exact resolve eq596010 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596010
  have eq596231 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq28 eq595880
    | exact resolve eq595880 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq595880
  have eq596241 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30 eq596152
    | exact resolve eq596152 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq596152
  have eq596275 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | exact superpose eq596231 eq382
    | exact resolve eq382 eq596231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq596231
  have eq596660 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have r₁ := eq596275
       have r₂ := eq587654
       grind)
    | exact resolve eq596275 eq587654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587654 eq596275
  have eq597600 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq596660
       grind)
    | exact superpose eq596660 eq44
    | exact resolve eq44 eq596660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq596660
  have eq597801 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq597600
    | exact resolve eq597600 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597600
  have eq624317 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq596241 eq24866
    | exact resolve eq24866 eq596241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24866 eq596241
  have eq624361 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq624317
  have eq647407 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq624361 eq597801
    | exact resolve eq597801 eq624361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597801 eq624361
  have eq647412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq647407
  have eq647430 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq647412
       have r₂ := eq27
       grind)
    | exact resolve eq647412 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647412
  have eq647433 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq647430 eq27
    | exact resolve eq27 eq647430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647430
  have eq647534 : x = y := by
    first
    | (have r₁ := eq647433
       have r₂ := eq589014
       grind)
    | exact resolve eq647433 eq589014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589014 eq647433
  have eq647536 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq647534
       grind)
    | exact superpose eq647534 eq18
    | exact resolve eq18 eq647534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq647537 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq647534
       grind)
    | exact superpose eq647534 eq24
    | exact resolve eq24 eq647534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq647534
  have eq648673 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq647537
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq647537
    | exact resolve eq647537 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq647537
  have eq648860 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq648673 eq26
    | exact resolve eq26 eq648673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq648673
  have eq651052 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq648860 eq119
    | exact resolve eq119 eq648860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq648860
  have eq651450 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq651052
       have i₂ := eq647536
       grind)
    | exact superpose eq647536 eq651052
    | exact resolve eq651052 eq647536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647536 eq651052
  have eq651617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq651450 eq15
    | exact resolve eq15 eq651450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651450
  have eq652315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq651617
    | exact resolve eq651617 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq651617
  have eq652538 : False := by grind
  exact eq652538

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pxx_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq93 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
    | (have r₁ := eq115 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq115 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq43
    | exact resolve eq43 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
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
  clear eq121
  have eq124 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq116 sF2
       grind)
    | exact superpose eq116 eq119
    | exact resolve eq119 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq144 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq116 sF1
       grind)
    | exact superpose eq116 eq141
    | exact resolve eq141 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq147 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq116 sF0
       grind)
    | exact superpose eq116 eq144
    | exact resolve eq144 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq256 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq320 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq322 eq51
    | exact resolve eq51 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq736 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq750 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq736 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq751 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq750 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq756 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq751 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq751
    | (have j0 := eq751 X0 X1
       grind)
    | exact resolve eq751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq757 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq756 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq4679 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq757 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq757
    | (have j0 := eq757 x X0
       grind)
    | exact resolve eq757 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq9114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq94 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9114
    | exact resolve eq9114 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9114
  have eq9126 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9115
       have r₂ := eq27
       grind)
    | exact resolve eq9115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9115
  have eq9130 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9126
    | exact resolve eq9126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9126
  have eq9132 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9130
    | exact resolve eq9130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9130
  have eq9134 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9132 eq322
    | exact resolve eq322 eq9132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq9135 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9132 eq334
    | exact resolve eq334 eq9132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9132
  have eq9342 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9135 eq9134
    | exact resolve eq9134 eq9135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9134 eq9135
  have eq9398 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq9342
  have eq9407 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq320 x
       have i₂ := eq9398
       grind)
    | exact superpose eq9398 eq320
    | exact resolve eq320 eq9398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9408 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq332 y
       have i₂ := eq9398
       grind)
    | exact superpose eq9398 eq332
    | exact resolve eq332 eq9398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9398
  have eq9562 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9407 eq147
    | exact resolve eq147 eq9407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9407
  have eq9637 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9562
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9562
    | exact resolve eq9562 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9562
  have eq9646 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9408 eq147
    | exact resolve eq147 eq9408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq9408
  have eq9726 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9646
    | exact resolve eq9646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9646
  have eq9998 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9726 eq9637
    | exact resolve eq9637 eq9726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9637 eq9726
  have eq10041 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq9998
  have eq10066 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10041 eq27
    | exact resolve eq27 eq10041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10069 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10041 eq257
    | exact resolve eq257 eq10041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq10084 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10041 eq367
    | exact resolve eq367 eq10041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq10098 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10069 eq334
    | exact resolve eq334 eq10069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq10069
  have eq10136 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10041 eq10098
    | exact resolve eq10098 eq10041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10041 eq10098
  have eq10172 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq10136
  have eq10699 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (k (M.op (σ x) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10084 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq10084
       grind)
    | exact resolve eq13 eq10084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10084
  have eq10741 : (k (M.op (σ x) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10699
       have r₂ := eq10172
       grind)
    | exact resolve eq10699 eq10172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10699
  have eq10746 : (σ x) = (k (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10741
       have i₂ := eq52 sF2 sF2 sF2
       grind)
    | (have i₁ := eq10741
       have i₂ := eq52 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq52 eq10741
    | exact resolve eq10741 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq10741
  have eq10901 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10172 eq10746
    | exact resolve eq10746 eq10172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10172 eq10746
  have eq10905 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq10901
  have eq10913 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10905 eq60
    | exact resolve eq60 eq10905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10914 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10905 eq94
    | exact resolve eq94 eq10905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq10905
  have eq10927 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10914
  have eq10939 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10927
       have r₂ := eq10066
       grind)
    | exact resolve eq10927 eq10066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10066 eq10927
  have eq10940 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq10913
    | exact resolve eq10913 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10913
  have eq10947 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq320 x
       have i₂ := eq10939
       grind)
    | exact superpose eq10939 eq320
    | exact resolve eq320 eq10939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq10948 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq332 y
       have i₂ := eq10939
       grind)
    | exact superpose eq10939 eq332
    | exact resolve eq332 eq10939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10950 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq10939
       grind)
    | exact superpose eq10939 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq10939
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10939
       grind)
    | exact resolve eq12 eq10939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10939
  have eq10983 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10950
       have r₂ := eq18
       grind)
    | exact resolve eq10950 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10950
  have eq10985 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10983
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10983
    | exact resolve eq10983 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10983
  have eq10986 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10985
  have eq11122 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10948 eq10947
    | exact resolve eq10947 eq10948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10947 eq10948
  have eq11179 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq11122
  have eq11203 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq11179 eq29
    | exact resolve eq29 eq11179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11179
  have eq11309 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq11203
    | exact resolve eq11203 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11203
  have eq11310 : x = (M.op x y) ∨ x = y := by grind
  clear eq11309
  have eq11326 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq11310 eq20
    | exact resolve eq20 eq11310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11372 : x = (M.op (M.op x x) x) ∨ x = y := by
    first
    | exact superpose eq11310 eq256
    | exact resolve eq256 eq11310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq11451 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq11326
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11326
    | exact resolve eq11326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11326
  have eq11679 : x = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq332 (M.op x x)
       have i₂ := eq11372
       grind)
    | exact superpose eq11372 eq332
    | exact resolve eq332 eq11372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq11372
  have eq11725 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq11310 eq11679
    | exact resolve eq11679 eq11310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11310 eq11679
  have eq11760 : x = (M.op x x) ∨ x = y := by grind
  clear eq11725
  have eq11765 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq124
       have i₂ := eq11760
       grind)
    | exact superpose eq11760 eq124
    | exact resolve eq124 eq11760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11760
  have eq11831 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11765
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11765
    | exact resolve eq11765 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11765
  have eq27317 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10940
       have i₂ := eq10986
       grind)
    | exact superpose eq10986 eq10940
    | exact resolve eq10940 eq10986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10940 eq10986
  have eq27323 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq27317
  have eq27345 : (k x y) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27323 eq60
    | exact resolve eq60 eq27323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq27323
  have eq27480 : (k x x) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49 eq27345
    | exact resolve eq27345 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq27345
  have eq27501 : (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27480
       have i₂ := eq116 x
       grind)
    | exact superpose eq116 eq27480
    | exact resolve eq27480 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq27480
  have eq27504 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq27501
       have r₂ := eq66
       grind)
    | exact resolve eq27501 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq27501
  have eq27726 : (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq27504
       grind)
    | exact superpose eq27504 eq44
    | exact resolve eq44 eq27504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27504
  have eq27751 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq27726
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq27726
    | exact resolve eq27726 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq27726
  have eq31417 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4679 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4679
    | (have j0 := eq4679 y
       grind)
    | exact resolve eq4679 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq31481 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31417
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq31417
    | exact resolve eq31417 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq31417
  have eq31505 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27751 eq31481
    | exact resolve eq31481 eq27751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27751 eq31481
  have eq31518 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq31505
    | exact resolve eq31505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31505
  have eq31529 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq31518
    | exact resolve eq31518 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31518
  have eq31553 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31529 eq11831
    | exact resolve eq11831 eq31529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11831 eq31529
  have eq31640 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31553
  have eq31653 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq31640 eq27
    | exact resolve eq27 eq31640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31640
  have eq31735 : x = y := by
    first
    | (have r₁ := eq31653
       have r₂ := eq11451
       grind)
    | exact resolve eq31653 eq11451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11451 eq31653
  have eq31736 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31735
       grind)
    | exact superpose eq31735 eq18
    | exact resolve eq18 eq31735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31737 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq31735
       grind)
    | exact superpose eq31735 eq24
    | exact resolve eq24 eq31735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31735
  have eq31874 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31737
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31737
    | exact resolve eq31737 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31737
  have eq31898 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31874 eq26
    | exact resolve eq26 eq31874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq31874
  have eq32219 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31898 eq122
    | exact resolve eq122 eq31898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq31898
  have eq32332 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32219
       have i₂ := eq31736
       grind)
    | exact superpose eq31736 eq32219
    | exact resolve eq32219 eq31736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31736 eq32219
  have eq32346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32332 eq15
    | exact resolve eq15 eq32332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32332
  have eq32426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq32346
    | exact resolve eq32346 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32346
  have eq32446 : False := by grind
  exact eq32446

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq61 X3 X0 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq350 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq351 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq352 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq347 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq347 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq347 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq368 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq352 (σ X0)
       grind)
    | exact superpose eq352 eq15
    | exact resolve eq15 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq368
    | exact resolve eq368 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq368
  have eq482 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq351 (σ X1) (σ X0)
       grind)
    | exact superpose eq351 eq15
    | (have j1 := eq351 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq351 (τ X1) X0
       grind)
    | exact superpose eq351 eq17
    | (have j1 := eq351 (τ X1) X0
       grind)
    | exact resolve eq17 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq351
  have eq1070 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq490 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq490
    | exact resolve eq490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1070 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1070
    | (have j0 := eq1070 X0 X1
       grind)
    | exact resolve eq1070 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1877 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq482 x y
       grind)
    | exact superpose eq482 eq16
    | (have j1 := eq482 x y
       grind)
    | exact resolve eq16 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1922 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq2066 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1877
       have i₂ := eq1131 y x
       grind)
    | exact superpose eq1131 eq1877
    | (have j1 := eq1131 (σ y) (σ x)
       grind)
    | (have r₁ := eq1877
       have r₂ := eq1131 y x
       grind)
    | exact resolve eq1877 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq2067 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2066
  have eq2074 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2067
       grind)
    | exact superpose eq2067 eq61
    | exact resolve eq61 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2075 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y x
       have i₂ := eq2067
       grind)
    | exact superpose eq2067 eq62
    | exact resolve eq62 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2136 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2075 y
       have i₂ := eq2067
       grind)
    | exact superpose eq2067 eq2075
    | exact resolve eq2075 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067 eq2075
  have eq2153 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2136
  have eq2164 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq2153
       grind)
    | exact superpose eq2153 eq61
    | exact resolve eq61 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq2314 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2164 (M.op x (σ x))
       have i₂ := eq2164 x
       grind)
    | exact superpose eq2164 eq2164
    | exact resolve eq2164 eq2164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164
  have eq2341 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2314
  have eq2345 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2341
       have i₂ := eq387 x
       grind)
    | exact superpose eq387 eq2341
    | exact resolve eq2341 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341
  have eq2377 : ∀ X0 X1 : G, (σ x) = (σ (M.op x x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq69 x X1 x x
       have i₂ := eq2345
       grind)
    | exact superpose eq2345 eq69
    | exact resolve eq69 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2345
  have eq2731 : ∀ X0 X1 : G, (M.op x x) = (τ (σ x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2377 X0 X1
       grind)
    | exact superpose eq2377 eq10
    | (have j1 := eq2377 X0 X1
       grind)
    | exact resolve eq10 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq2790 : ∀ X0 X1 : G, x = (M.op x x) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2731 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2731
    | (have j0 := eq2731 X0 X1
       grind)
    | exact resolve eq2731 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731
  have eq2822 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op (M.op (M.op X1 X2) x) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 x X1 x
       have i₂ := eq2790 X0 X1
       grind)
    | exact superpose eq2790 eq67
    | (have j1 := eq2790 X1 X2
       grind)
    | exact resolve eq67 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790
  have eq2884 : ∀ X0 X1 : G, x ≠ x ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2822 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822
  have eq2885 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2884 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884
  have eq2941 : x = (M.op x x) := by
    first
    | (have i₁ := eq2885 (M.op x x) x
       have i₂ := eq2885 x x
       grind)
    | exact superpose eq2885 eq2885
    | exact resolve eq2885 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2958 : ∀ X2 : G, x = (M.op x (M.op x X2)) := by
    intro X2
    first
    | (have i₁ := eq61 (M.op (M.op x x) x) x X2
       have i₂ := eq2885 x x
       grind)
    | exact superpose eq2885 eq61
    | exact resolve eq61 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2962 : ∀ X2 : G, x = (M.op (M.op X2 x) x) := by
    intro X2
    first
    | (have i₁ := eq67 x x (M.op (M.op x x) x)
       have i₂ := eq2885 x x
       grind)
    | exact superpose eq2885 eq67
    | exact resolve eq67 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2885
  have eq3023 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (M.op (M.op x X0) x) ∨ (M.op x x) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op x X0) x
       have i₂ := eq2958 X0
       grind)
    | exact superpose eq2958 eq13
    | (have j0 := eq13 (M.op x X0) x
       grind)
    | (have r₁ := eq13 (M.op x x) x
       have r₂ := eq2958 x
       grind)
    | exact resolve eq13 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958
  have eq3035 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) x) ∨ (M.op x x) = (k (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq3023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023
  have eq3037 : ∀ X0 : G, x = (k (M.op x X0) x) ∨ (M.op x X0) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq3035 X0
       have i₂ := eq2941
       grind)
    | exact superpose eq2941 eq3035
    | (have j0 := eq3035 X0
       grind)
    | exact resolve eq3035 eq2941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq3815 : x = (k y x) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3037 (M.op y x)
       have i₂ := eq2074 x
       grind)
    | exact superpose eq2074 eq3037
    | exact resolve eq3037 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074 eq3037
  have eq12674 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1922 x y
       have i₂ := eq3815
       grind)
    | exact superpose eq3815 eq1922
    | (have j0 := eq1922 x y
       grind)
    | exact resolve eq1922 eq3815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922 eq3815
  have eq12691 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq12674
  have eq12692 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12691
  have eq12713 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2962 y
       have i₂ := eq12692
       grind)
    | exact superpose eq12692 eq2962
    | exact resolve eq2962 eq12692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962
  have eq12753 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12692
       have i₂ := eq12713
       grind)
    | exact superpose eq12713 eq12692
    | exact resolve eq12692 eq12713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12692 eq12713
  have eq12788 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12753
  have eq12792 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12788
       grind)
    | exact superpose eq12788 eq16
    | exact resolve eq16 eq12788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12788
  have eq12829 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12792
       have r₂ := eq387 x
       grind)
    | exact resolve eq12792 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12792
  have eq12835 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12829
       grind)
    | exact superpose eq12829 eq16
    | exact resolve eq16 eq12829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12851 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq12829
       grind)
    | exact superpose eq12829 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12829
       grind)
    | exact resolve eq12 eq12829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12852 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq12829
       grind)
    | exact superpose eq12829 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12829
       grind)
    | exact resolve eq13 eq12829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12854 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq12829
       grind)
    | exact superpose eq12829 eq61
    | exact resolve eq61 eq12829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq12874 : (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq12852
  have eq12875 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
  clear eq12851
  have eq12881 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12874
       have i₂ := eq387 x
       grind)
    | exact superpose eq387 eq12874
    | exact resolve eq12874 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq12874
  have eq12882 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq12875
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq12875
    | exact resolve eq12875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12875
  have eq12894 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12881
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12881
    | exact resolve eq12881 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12881
  have eq12899 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12894
       have i₂ := eq2941
       grind)
    | exact superpose eq2941 eq12894
    | exact resolve eq12894 eq2941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12894
  have eq12903 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq12899
       have i₂ := eq12882
       grind)
    | exact superpose eq12882 eq12899
    | exact resolve eq12899 eq12882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12899
  have eq13156 : (σ y) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq12854 (σ x)
       have i₂ := eq12882
       grind)
    | exact superpose eq12882 eq12854
    | exact resolve eq12854 eq12882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12854 eq12882
  have eq14354 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1131 y x
       have i₂ := eq12903
       grind)
    | exact superpose eq12903 eq1131
    | (have j0 := eq1131 y x
       grind)
    | exact resolve eq1131 eq12903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq12903
  have eq14421 : x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq14354
       have r₂ := eq12835
       grind)
    | exact resolve eq14354 eq12835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14354
  have eq14488 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq12835
       have i₂ := eq14421
       grind)
    | exact superpose eq14421 eq12835
    | exact resolve eq12835 eq14421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14421
  have eq14525 : (σ y) = (σ (k x y)) := by grind
  clear eq14488
  have eq14546 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13156
       have i₂ := eq14525
       grind)
    | exact superpose eq14525 eq13156
    | exact resolve eq13156 eq14525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13156 eq14525
  have eq14624 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14546
       have i₂ := eq12829
       grind)
    | exact superpose eq12829 eq14546
    | exact resolve eq14546 eq12829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12829 eq14546
  have eq14717 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14624
       grind)
    | exact superpose eq14624 eq10
    | exact resolve eq10 eq14624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14624
  have eq14790 : x = y := by
    first
    | (have i₁ := eq14717
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14717
    | exact resolve eq14717 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14717
  have eq14837 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12835
       have i₂ := eq14790
       grind)
    | exact superpose eq14790 eq12835
    | exact resolve eq12835 eq14790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12835 eq14790
  have eq14868 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq14837
       have i₂ := eq2941
       grind)
    | exact superpose eq2941 eq14837
    | exact resolve eq14837 eq2941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2941 eq14837
  have eq14869 : False := by grind
  exact eq14869

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
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
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq16 X0 x x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq177 X2 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq812
       grind)
    | exact superpose eq812 eq40
    | exact resolve eq40 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq812
  have eq844 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq843
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq843
    | exact resolve eq843 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq846 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq844
    | exact resolve eq844 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq846 eq817
    | exact resolve eq817 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq863 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq856
       have r₂ := eq27
       grind)
    | exact resolve eq856 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq868 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq863 eq186
    | exact resolve eq186 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq870 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq863 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq863
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq863
       grind)
    | exact resolve eq12 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq863 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq863 eq177
    | exact resolve eq177 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq876 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq863 eq177
    | exact resolve eq177 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq883 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq870
  have eq885 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq871
    | exact resolve eq871 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq886 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq846 eq883
    | exact resolve eq883 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq846 eq885
    | exact resolve eq885 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq885
  have eq889 : (σ x) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq888
       have r₂ := eq27
       grind)
    | exact resolve eq888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq965 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq868 eq875
    | exact resolve eq875 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq981 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq965
  have eq986 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq981 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq981
       grind)
    | exact resolve eq13 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq997 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq986
  have eq1001 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq997 eq153
    | exact resolve eq153 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1004 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq1001
    | exact resolve eq1001 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1009 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq822 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq822
    | (have j0 := eq822 y
       grind)
    | (have r₁ := eq822 y
       have r₂ := eq1004
       grind)
    | exact resolve eq822 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq1004
  have eq1010 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq1009
  have eq1014 : y = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq185 y
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq185
    | exact resolve eq185 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq178 y y x
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq178
    | exact resolve eq178 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1029 : y ≠ y ∨ (k (M.op x y) y) = (M.op y (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1014 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq1014
       grind)
    | exact resolve eq13 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1041 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ y = (M.op y x) := by grind
  clear eq1029
  have eq1166 : y = (M.op y (k (M.op x y) y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1041 eq1020
    | exact resolve eq1020 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq1041
  have eq1181 : y = (M.op y (k (M.op x y) y)) ∨ y = (M.op y x) := by grind
  clear eq1166
  have eq1246 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq886 eq876
    | exact resolve eq876 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq1255 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq886 eq178
    | exact resolve eq178 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq1261 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1246
  have eq1263 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1255 X0
       grind)
    | (have r₁ := eq1255 X0
       have r₂ := eq889
       grind)
    | exact resolve eq1255 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1271 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1261
       have r₂ := eq889
       grind)
    | exact resolve eq1261 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq1261
  have eq1296 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1271 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq28 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq2659 : (τ (σ x)) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1296 eq133
    | exact resolve eq133 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1296
  have eq2668 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (k (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq2659
    | exact resolve eq2659 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659
  have eq2700 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y x) ∨ x = (k (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2668 eq875
    | exact resolve eq875 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq2668
  have eq2721 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y x) ∨ x = (k (M.op x y) y) := by grind
  clear eq2700
  have eq2733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq2721 eq1263
    | exact resolve eq1263 eq2721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq2721
  have eq2758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (k (M.op x y) y) := by grind
  clear eq2733
  have eq2763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq26 eq2758
    | exact resolve eq2758 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758
  have eq2767 : y = (M.op y x) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq2763
       have r₂ := eq27
       grind)
    | exact resolve eq2763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq2772 : y = (M.op (M.op x y) y) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq185 x
       have i₂ := eq2767
       grind)
    | exact superpose eq2767 eq185
    | exact resolve eq185 eq2767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2773 : x = (k (M.op x y) y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq2767
       grind)
    | exact superpose eq2767 eq189
    | exact resolve eq189 eq2767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767
  have eq2804 : y ≠ y ∨ (k (M.op x y) y) = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq2772 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq2772
       grind)
    | exact resolve eq13 eq2772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2772
  have eq2821 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) := by grind
  clear eq2804
  have eq2823 : x = (k (M.op x y) y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq2773 eq2821
    | exact resolve eq2821 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773 eq2821
  have eq2824 : x = (k (M.op x y) y) := by grind
  clear eq2823
  have eq2828 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2824 eq1181
    | exact resolve eq1181 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq2832 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2824 eq41
    | exact resolve eq41 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2835 : y = (M.op y x) := by grind
  clear eq2828
  have eq2836 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq2832
    | exact resolve eq2832 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2832
  have eq2838 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2836
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2836
    | exact resolve eq2836 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2836
  have eq2842 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq185 x
       have i₂ := eq2835
       grind)
    | exact superpose eq2835 eq185
    | exact resolve eq185 eq2835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq2843 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq2835
       grind)
    | exact superpose eq2835 eq189
    | exact resolve eq189 eq2835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq2849 : ∀ X0 : G, y = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y x
       have i₂ := eq2835
       grind)
    | exact superpose eq2835 eq177
    | exact resolve eq177 eq2835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2835
  have eq2887 : y = (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2842 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2902 : y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2843 eq2887
    | exact resolve eq2887 eq2843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843 eq2887
  have eq2966 : y = (M.op y y) := by
    first
    | exact superpose eq2842 eq2849
    | exact resolve eq2849 eq2842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842 eq2849
  have eq3004 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2966
       grind)
    | exact superpose eq2966 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq2966
       grind)
    | exact resolve eq13 eq2966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3021 : y = (k y y) := by grind
  clear eq3004
  have eq3023 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3021
       grind)
    | exact superpose eq3021 eq41
    | exact resolve eq41 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3021
  have eq3029 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3023
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3023
    | exact resolve eq3023 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023
  have eq3035 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3029 eq778
    | (have j0 := eq778 (σ y) (σ y)
       grind)
    | (have r₁ := eq778 (σ y) (σ y)
       have r₂ := eq3029
       grind)
    | exact resolve eq778 eq3029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3029
  have eq3036 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3035
  have eq3037 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3036
  have eq3055 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq3037 eq178
    | exact resolve eq178 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3061 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq3037 eq192
    | exact resolve eq192 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3526 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) (M.op X0 (σ y))) = (k (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq3061 eq13
    | (have j0 := eq13 (M.op X0 (σ y)) (σ y)
       grind)
    | (have r₁ := eq13 (M.op X0 (σ y)) (σ y)
       have r₂ := eq3061 X0
       grind)
    | exact resolve eq13 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061
  have eq3545 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (k (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3526 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3714 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2902 eq42
    | exact resolve eq42 eq2902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2902
  have eq3718 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq3714
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3714
    | exact resolve eq3714 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3714
  have eq3737 : (σ y) ≠ (σ y) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3718 eq778
    | (have j0 := eq778 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq778 (σ y) (σ (M.op x y))
       have r₂ := eq3718
       grind)
    | exact resolve eq778 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq3738 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq3737
  have eq3739 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2838 eq3738
    | exact resolve eq3738 eq2838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2838 eq3738
  have eq4702 : ∀ X0 : G, (σ y) = (M.op (σ y) (k (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq3545 eq3055
    | exact resolve eq3055 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055
  have eq4706 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (M.op (σ y) X0) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq3545 eq178
    | exact resolve eq178 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq4707 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (k (M.op X0 (σ y)) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq3545 eq192
    | exact resolve eq192 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq3545
  have eq4767 : ∀ X0 : G, (σ y) = (k (k (M.op X0 (σ y)) (σ y)) (σ y)) ∨ (k (M.op X0 (σ y)) (σ y)) = (M.op (k (M.op X0 (σ y)) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq4702 eq28
    | (have j0 := eq28 (k (M.op X0 (σ y)) (σ y)) (σ y)
       grind)
    | exact resolve eq28 eq4702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4785 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (k (k (M.op X0 (σ y)) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq4707 eq4767
    | (have j0 := eq4767 X0
       grind)
    | exact resolve eq4767 eq4707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4767
  have eq5035 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (k (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (k (M.op X0 (σ y)) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq4707 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | exact resolve eq12 eq4707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5036 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op (σ y) (k (M.op X0 (σ y)) (σ y))) = (k (k (M.op X0 (σ y)) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq4707 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq4707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4707
  have eq5055 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k (k (M.op X0 (σ y)) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq4702 eq5036
    | (have j0 := eq5036 X0
       grind)
    | exact resolve eq5036 eq4702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4702 eq5036
  have eq5056 : ∀ X0 : G, (σ y) = (k (k (M.op X0 (σ y)) (σ y)) (σ y)) ∨ (M.op X0 (σ y)) ≠ (k (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq3037 eq5035
    | (have j0 := eq5035 X0
       grind)
    | exact resolve eq5035 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035
  have eq5063 : ∀ X0 : G, (σ y) = (k (k (M.op X0 (σ y)) (σ y)) (σ y)) ∨ (M.op X0 (σ y)) ≠ (k (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq5056 X0
       have j1 := eq5055 X0
       grind)
    | (have r₁ := eq5056 X0
       have r₂ := eq5055 X0
       grind)
    | exact resolve eq5056 eq5055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055 eq5056
  have eq5064 : ∀ X0 : G, (σ y) = (k (k (M.op X0 (σ y)) (σ y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq5063 X0
       have j1 := eq4785 X0
       grind)
    | (have r₁ := eq5063 X0
       have r₂ := eq4785 X0
       grind)
    | exact resolve eq5063 eq4785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4785 eq5063
  have eq5159 : ∀ X0 : G, (σ y) = (k (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq4706 eq5064
    | exact resolve eq5064 eq4706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4706 eq5064
  have eq5195 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op (σ y) X0)) y) := by
    intro X0
    first
    | exact superpose eq5159 eq153
    | exact resolve eq153 eq5159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq5159
  have eq5199 : ∀ X0 : G, y = (k (τ (M.op (σ y) X0)) y) := by
    intro X0
    first
    | exact superpose eq32 eq5195
    | exact resolve eq5195 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5195
  have eq6585 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3739 eq177
    | exact resolve eq177 eq3739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq3739
  have eq9786 : y = (k (τ (σ (M.op x y))) y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq6585 eq5199
    | exact resolve eq5199 eq6585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199 eq6585
  have eq9812 : y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq29 eq9786
    | exact resolve eq9786 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9786
  have eq9818 : x = y ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2824 eq9812
    | exact resolve eq9812 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824 eq9812
  have eq9819 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq9818
  have eq10132 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3718 eq781
    | (have j0 := eq781 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq781 eq3718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq3718
  have eq10198 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9819 eq10132
    | (have j0 := eq10132 X0
       grind)
    | exact resolve eq10132 eq9819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10132
  have eq11636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq9819 eq10198
    | exact resolve eq10198 eq9819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9819 eq10198
  have eq11700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11636
  have eq11718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq11700
    | exact resolve eq11700 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11700
  have eq11727 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11718
       have r₂ := eq27
       grind)
    | exact resolve eq11718 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11718
  have eq11736 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11727 eq32
    | exact resolve eq32 eq11727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq11727
  have eq11923 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq11736
    | exact resolve eq11736 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11736
  have eq11924 : x = y := by grind
  clear eq11923
  have eq11933 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11924
       grind)
    | exact superpose eq11924 eq18
    | exact resolve eq18 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq11934 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq11924
       grind)
    | exact superpose eq11924 eq24
    | exact resolve eq24 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq11994 : x = (M.op x x) := by
    first
    | (have i₁ := eq2966
       have i₂ := eq11924
       grind)
    | exact superpose eq11924 eq2966
    | exact resolve eq2966 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2966 eq11924
  have eq12047 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11934
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11934
    | exact resolve eq11934 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11934
  have eq12048 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12047 eq26
    | exact resolve eq26 eq12047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq12105 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12047 eq3037
    | exact resolve eq3037 eq12047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3037 eq12047
  have eq12214 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12105 eq12048
    | exact resolve eq12048 eq12105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12048 eq12105
  have eq12221 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq12214 eq27
    | exact resolve eq27 eq12214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12214
  have eq12895 : x = (M.op x y) := by
    first
    | (have i₁ := eq11933
       have i₂ := eq11994
       grind)
    | exact superpose eq11994 eq11933
    | exact resolve eq11933 eq11994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11933 eq11994
  have eq12938 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq12895
       grind)
    | exact superpose eq12895 eq22
    | exact resolve eq22 eq12895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12895
  have eq13088 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12938 eq20
    | exact resolve eq20 eq12938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12938
  have eq13156 : False := by grind
  exact eq13156

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_pxy_pxx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq43
    | exact resolve eq43 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq76 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq73
    | exact resolve eq73 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq81 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq121 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq117
    | exact resolve eq117 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq123 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq121
    | exact resolve eq121 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq140 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X2 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have i₂ := eq14 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq123
       grind)
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq165 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq162
       have i₂ := eq70 sF1
       grind)
    | exact superpose eq70 eq162
    | exact resolve eq162 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq167 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq165
       have i₂ := eq70 sF0
       grind)
    | exact superpose eq70 eq165
    | exact resolve eq165 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq165
  have eq188 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq167 eq16
    | exact resolve eq16 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : x = (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq305 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq52 X2 X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X0 ∨ (M.op X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81 (M.op x x) X1
       have i₂ := eq52 x x x
       grind)
    | exact superpose eq52 eq81
    | exact resolve eq81 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq341 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq305 eq50
    | exact resolve eq50 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq343 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq305 eq52
    | exact resolve eq52 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq411 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq1035 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X0) x
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1131 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq411 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq411
    | (have j0 := eq411 X0 x
       grind)
    | exact resolve eq411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1133 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq411
    | (have j0 := eq411 X0 (M.op x y)
       grind)
    | exact resolve eq411 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq1157 : (k (M.op (M.op x y) (M.op x y)) x) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x))) := by
    first
    | exact superpose eq188 eq1131
    | exact resolve eq1131 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq1131
  have eq1214 : (k (M.op y y) (M.op x y)) = (τ (k (M.op (σ y) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq146 eq1133
    | exact resolve eq1133 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq1133
  have eq1869 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 x X0
       have i₂ := eq53 X0 x (M.op X0 x)
       grind)
    | exact superpose eq53 eq140
    | (have j0 := eq140 X0 X1 X0
       grind)
    | (have r₁ := eq140 X0 x X0
       have r₂ := eq53 X0 x (M.op X0 x)
       grind)
    | exact resolve eq140 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq1882 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1869 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq4947 : (τ (σ (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq1157
       have i₂ := eq326 sF1 sF2
       grind)
    | exact superpose eq326 eq1157
    | (have j1 := eq326 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq1157 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq4977 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq30 eq4947
    | exact resolve eq4947 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4947
  have eq5476 : (τ (σ y)) = (k (M.op y y) (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq1214
       have i₂ := eq326 sF3 sF1
       grind)
    | exact superpose eq326 eq1214
    | (have j1 := eq326 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq1214 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq1214
  have eq5506 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (k (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq29 eq5476
    | exact resolve eq5476 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5476
  have eq27734 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq4977 eq53
    | exact resolve eq53 eq4977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq4977
  have eq31037 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) ∨ y = (k (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq5506 eq27734
    | exact resolve eq27734 eq5506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) ∨ y = (k (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq26 eq31037
    | exact resolve eq31037 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31037
  have eq31078 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) ∨ y = (k (M.op y y) (M.op x y)) := by
    first
    | (have r₁ := eq31077
       have r₂ := eq27
       grind)
    | exact resolve eq31077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31077
  have eq38645 : (k (M.op (M.op x y) (M.op x y)) x) = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1882 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1882
    | (have j0 := eq1882 x y
       grind)
    | exact resolve eq1882 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38648 : (k (M.op y y) (M.op x y)) = (M.op (M.op y y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq305 eq1882
    | exact resolve eq1882 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882
  have eq225103 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ (M.op x y) = (M.op x x) ∨ y = (k (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq31078 eq38645
    | exact resolve eq38645 eq31078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31078
  have eq225783 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ (M.op x y) = (M.op x x) ∨ y = (k (M.op y y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq225103 eq308
    | exact resolve eq308 eq225103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq225103
  have eq226085 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ y = (k (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq266 eq225783
    | exact resolve eq225783 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq225783
  have eq226209 : y = (k (M.op y y) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq226085
  have eq226223 : y = (M.op (M.op y y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq38648 eq226209
    | exact resolve eq226209 eq38648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226209
  have eq226634 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq226223 eq343
    | exact resolve eq343 eq226223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226223
  have eq226764 : y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq305 y
       have i₂ := eq226634
       grind)
    | exact superpose eq226634 eq305
    | exact resolve eq305 eq226634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226634
  have eq226882 : (M.op x y) = (M.op x x) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq226764
  have eq226967 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq315 x
       have i₂ := eq226882
       grind)
    | exact superpose eq226882 eq315
    | exact resolve eq315 eq226882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226978 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1035 x x
       have i₂ := eq226882
       grind)
    | exact superpose eq226882 eq1035
    | exact resolve eq1035 eq226882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq226882
  have eq227104 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq226978
    | (have j0 := eq226978 X0
       grind)
    | exact resolve eq226978 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226978
  have eq227129 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq227104 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq227104
    | (have j0 := eq227104 X0
       grind)
    | exact resolve eq227104 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227104
  have eq227588 : x ≠ y ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq226967
  have eq229726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (k (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq5506 eq227129
    | exact resolve eq227129 eq5506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5506 eq227129
  have eq229835 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (k (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq26 eq229726
    | exact resolve eq229726 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229726
  have eq229838 : y = (k (M.op y y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq229835
       have r₂ := eq27
       grind)
    | exact resolve eq229835 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229835
  have eq233761 : y = (M.op (M.op y y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq229838 eq38648
    | exact resolve eq38648 eq229838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38648 eq229838
  have eq233812 : y = (M.op (M.op y y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq233761
  have eq239566 : (M.op x y) = (M.op y y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq233812 eq343
    | exact resolve eq343 eq233812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq233812
  have eq239699 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq305 y
       have i₂ := eq239566
       grind)
    | exact superpose eq239566 eq305
    | exact resolve eq305 eq239566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq239566
  have eq239821 : y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq239699
  have eq239886 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq239821 eq167
    | exact resolve eq167 eq239821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq239896 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq239821 eq341
    | exact resolve eq341 eq239821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq239922 : (k y x) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq239821 eq38645
    | exact resolve eq38645 eq239821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38645
  have eq240392 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq239886
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq239886
    | exact resolve eq239886 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239886
  have eq240411 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq239896
       grind)
    | exact superpose eq239896 eq123
    | exact resolve eq123 eq239896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239896
  have eq240626 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq240411
    | exact resolve eq240411 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq240411
  have eq242820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq240392 eq27734
    | exact resolve eq27734 eq240392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27734 eq240392
  have eq242971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq26 eq242820
    | exact resolve eq242820 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242820
  have eq243186 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have r₁ := eq242971
       have r₂ := eq27
       grind)
    | exact resolve eq242971 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242971
  have eq243378 : (M.op x y) = (k y x) := by
    first
    | exact superpose eq239821 eq243186
    | exact resolve eq243186 eq239821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243186
  have eq433564 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq239922
       have i₂ := eq243378
       grind)
    | exact superpose eq243378 eq239922
    | exact resolve eq239922 eq243378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239922 eq243378
  have eq433572 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq315 y
       have i₂ := eq433564
       grind)
    | exact superpose eq433564 eq315
    | exact resolve eq315 eq433564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433564
  have eq433688 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq239821 eq433572
    | exact resolve eq433572 eq239821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433572
  have eq433731 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq315 x
       have i₂ := eq433688
       grind)
    | exact superpose eq433688 eq315
    | exact resolve eq315 eq433688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq433688
  have eq433928 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq433731
       have r₂ := eq227588
       grind)
    | exact resolve eq433731 eq227588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227588 eq433731
  have eq433976 : x = y := by
    first
    | exact superpose eq239821 eq433928
    | exact resolve eq433928 eq239821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239821 eq433928
  have eq433996 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq433976
       grind)
    | exact superpose eq433976 eq24
    | exact resolve eq24 eq433976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq434005 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq433976
       grind)
    | exact superpose eq433976 eq123
    | exact resolve eq123 eq433976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq433976
  have eq434405 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq434005
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq434005
    | exact resolve eq434005 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq434005
  have eq434413 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq433996
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq433996
    | exact resolve eq433996 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq433996
  have eq434483 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq240626 eq434405
    | exact resolve eq434405 eq240626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240626 eq434405
  have eq434579 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq434413 eq26
    | exact resolve eq26 eq434413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq434413
  have eq438013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq434483 eq434579
    | exact resolve eq434579 eq434483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434483 eq434579
  have eq438014 : False := by grind
  exact eq438014

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = Y then X else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pxx_x_y_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq49 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq54 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq79 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y X0
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 X0 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq84 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq54 X2 X0 x
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq79 eq54
    | exact resolve eq54 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq82 eq54
    | exact resolve eq54 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq54 X0 X0 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
    | (have i₁ := eq15 X0 X0
       have i₂ := eq102 (σ X0)
       grind)
    | exact superpose eq102 eq15
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq112
    | exact resolve eq112 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq112
  have eq140 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq186 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq10
    | exact resolve eq10 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 (M.op X0 X0)
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq29
    | exact resolve eq29 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq194 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq37
    | exact resolve eq37 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq198 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140
    | exact resolve eq140 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq233 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq186 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq186
    | exact resolve eq186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq375 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq14 sF3 sF1
       grind)
    | exact superpose eq14 eq43
    | (have j1 := eq14 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq43 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq189 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq189
    | (have j0 := eq189 x
       grind)
    | exact resolve eq189 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1241 : (M.op (σ x) (σ x)) = (σ (k (M.op x y) (M.op x x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1218 eq14
    | (have j0 := eq14 (σ x) (σ (k (M.op x y) (M.op x x)))
       grind)
    | exact resolve eq14 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1244 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (σ (k (M.op x y) (M.op x x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1241
       have i₂ := eq54 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1241
       have i₂ := eq54 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq54 eq1241
    | exact resolve eq1241 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq2269 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq194
    | (have j0 := eq194 (M.op x y)
       grind)
    | exact resolve eq194 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq2316 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2269 eq14
    | (have j0 := eq14 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2319 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2316
       have i₂ := eq54 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2316
       have i₂ := eq54 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq54 eq2316
    | exact resolve eq2316 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316
  have eq6968 : (M.op x y) ≠ (M.op x y) ∨ (M.op y y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq85 eq101
    | (have j0 := eq101 (M.op x y) y
       grind)
    | (have r₁ := eq101 (M.op x y) y
       have r₂ := eq85 (M.op x y)
       grind)
    | exact resolve eq101 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6969 : x ≠ x ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq82 eq101
    | (have j0 := eq101 x (M.op x y)
       grind)
    | (have r₁ := eq101 x (M.op x y)
       have r₂ := eq82 x
       grind)
    | exact resolve eq101 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq6975 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x x)) := by grind
  clear eq6969
  have eq6976 : (M.op y y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq6968
  have eq6980 : (M.op (σ x) (σ x)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6975 eq1244
    | exact resolve eq1244 eq6975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq6983 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6976 eq2319
    | exact resolve eq2319 eq6976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq6986 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6980
       have i₂ := eq113 sF0
       grind)
    | exact superpose eq113 eq6980
    | exact resolve eq6980 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6980
  have eq6989 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6983
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq6983
    | exact resolve eq6983 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6983
  have eq6992 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq6986
    | exact resolve eq6986 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6986
  have eq6993 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6992
  have eq6996 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6989
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6989
    | exact resolve eq6989 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989
  have eq6997 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6996
  have eq7364 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq6993 eq54
    | exact resolve eq54 eq6993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7368 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq6997 eq84
    | exact resolve eq84 eq6997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6997
  have eq7576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6993 eq7368
    | exact resolve eq7368 eq6993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6993 eq7368
  have eq7584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq7576
    | exact resolve eq7576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7576
  have eq7586 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq7584
       have r₂ := eq28
       grind)
    | exact resolve eq7584 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7584
  have eq7603 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7586 eq233
    | exact resolve eq233 eq7586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7608 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq7586 eq54
    | exact resolve eq54 eq7586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7613 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40 eq7603
    | exact resolve eq7603 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7603
  have eq7627 : (M.op y y) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7613
       have i₂ := eq233 sF1
       grind)
    | exact superpose eq233 eq7613
    | exact resolve eq7613 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7613
  have eq7628 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq38 eq7627
    | exact resolve eq7627 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7627
  have eq7656 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7628 eq233
    | exact resolve eq233 eq7628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7628
  have eq7666 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq39 eq7656
    | exact resolve eq7656 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7656
  have eq7680 : (M.op x x) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7666
       have i₂ := eq233 sF1
       grind)
    | exact superpose eq233 eq7666
    | exact resolve eq7666 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7666
  have eq7681 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq38 eq7680
    | exact resolve eq7680 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7680
  have eq7698 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq7681 eq90
    | exact resolve eq90 eq7681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq7681
  have eq7741 : (M.op x y) = (M.op (M.op x x) y) ∨ (M.op x y) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq7698 eq85
    | exact resolve eq85 eq7698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7698
  have eq12863 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7586 eq7608
    | exact resolve eq7608 eq7586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7586 eq7608
  have eq12876 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12863
  have eq12880 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12876
       have i₂ := eq54 sF1 sF1 sF1
       grind)
    | (have i₁ := eq12876
       have i₂ := eq54 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq54 eq12876
    | exact resolve eq12876 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq12876
  have eq12899 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12880 eq233
    | exact resolve eq233 eq12880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12880
  have eq12911 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq12899
    | exact resolve eq12899 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12899
  have eq12925 : (M.op x x) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12911
       have i₂ := eq233 sF1
       grind)
    | exact superpose eq233 eq12911
    | exact resolve eq12911 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12911
  have eq12926 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38 eq12925
    | exact resolve eq12925 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12925
  have eq12947 : (M.op x y) = (k (M.op x y) (M.op x x)) ∨ (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12926 eq58
    | exact resolve eq58 eq12926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq12967 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6975 eq12947
    | exact resolve eq12947 eq6975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6975 eq12947
  have eq12970 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq82 eq12967
    | exact resolve eq12967 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12967
  have eq13600 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12970 eq12926
    | exact resolve eq12926 eq12970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12926
  have eq13621 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq13600
  have eq13873 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82 x
       have i₂ := eq13621
       grind)
    | exact superpose eq13621 eq82
    | exact resolve eq82 eq13621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13621
  have eq13964 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13873 eq12970
    | exact resolve eq12970 eq13873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12970 eq13873
  have eq13985 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq13964
  have eq14001 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13985 eq40
    | exact resolve eq40 eq13985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14044 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq14001
    | exact resolve eq14001 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14001
  have eq14049 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14044 eq79
    | exact resolve eq79 eq14044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14050 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14044 eq82
    | exact resolve eq82 eq14044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14095 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq14044
  have eq14479 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14049 (M.op y x)
       have i₂ := eq14049 x
       grind)
    | exact superpose eq14049 eq14049
    | exact resolve eq14049 eq14049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14490 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq14479
  have eq14541 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113 y
       have i₂ := eq14490
       grind)
    | exact superpose eq14490 eq113
    | exact resolve eq113 eq14490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14490
  have eq14562 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14541
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14541
    | exact resolve eq14541 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14541
  have eq14565 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13985 eq14562
    | exact resolve eq14562 eq13985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13985 eq14562
  have eq14598 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq14565
  have eq14647 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14598 eq233
    | exact resolve eq233 eq14598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14598
  have eq14662 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq14647
    | exact resolve eq14647 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14647
  have eq14694 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14662 eq85
    | exact resolve eq85 eq14662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq14662
  have eq14767 : x = (M.op x y) ∨ (M.op x y) = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7741
       have i₂ := eq14050 x
       grind)
    | exact superpose eq14050 eq7741
    | exact resolve eq7741 eq14050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7741 eq14050
  have eq14774 : (M.op x y) = (M.op x (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq14767
  have eq14876 : (M.op y y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84 y x y
       have i₂ := eq14774
       grind)
    | exact superpose eq14774 eq84
    | exact resolve eq84 eq14774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq14774
  have eq15972 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14876 eq14694
    | exact resolve eq14694 eq14876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14694 eq14876
  have eq15982 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq15972
  have eq16007 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14049 y
       have i₂ := eq15982
       grind)
    | exact superpose eq15982 eq14049
    | exact resolve eq14049 eq15982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14049
  have eq16008 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq15982
       grind)
    | exact superpose eq15982 eq79
    | exact resolve eq79 eq15982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15982
  have eq16029 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq16007
  have eq16072 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16008 eq113
    | exact resolve eq113 eq16008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16008
  have eq16098 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq16072
    | exact resolve eq16072 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16072
  have eq16101 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16098
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16098
    | exact resolve eq16098 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16098
  have eq16270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16101 eq7364
    | exact resolve eq7364 eq16101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7364 eq16101
  have eq16305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq16270
    | exact resolve eq16270 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16270
  have eq16314 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16305
       have r₂ := eq28
       grind)
    | exact resolve eq16305 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16305
  have eq16369 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16314 eq233
    | exact resolve eq233 eq16314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq16314
  have eq16383 : (τ (σ y)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq16369
    | exact resolve eq16369 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq16369
  have eq16395 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40 eq16383
    | exact resolve eq16383 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16383
  have eq17459 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82 x
       have i₂ := eq16395
       grind)
    | exact superpose eq16395 eq82
    | exact resolve eq82 eq16395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16395
  have eq17525 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17459 eq16029
    | exact resolve eq16029 eq17459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16029 eq17459
  have eq17540 : x = y ∨ x = (M.op x y) := by grind
  clear eq17525
  have eq17548 : x = (M.op x y) := by
    first
    | (have r₁ := eq17540
       have r₂ := eq14095
       grind)
    | exact resolve eq17540 eq14095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14095 eq17540
  have eq17551 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17548 eq21
    | exact resolve eq21 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq17556 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq17548 eq38
    | exact resolve eq38 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq17558 : (k (σ y) (σ (M.op x y))) = (σ (k y x)) := by
    first
    | exact superpose eq17548 eq43
    | exact resolve eq43 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq17559 : ∀ X0 : G, y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq17548 eq79
    | exact resolve eq79 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq17560 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq17548 eq82
    | exact resolve eq82 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq17573 : (σ (M.op x y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17548 eq375
    | exact resolve eq375 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq18187 : (M.op y y) = (k y (M.op x x)) := by
    first
    | exact superpose eq17548 eq6976
    | exact resolve eq6976 eq17548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6976 eq17548
  have eq19658 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17551
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17551
    | exact resolve eq17551 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17551
  have eq19893 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19658 eq23
    | exact resolve eq23 eq19658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq19894 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq19658 eq27
    | exact resolve eq27 eq19658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19658
  have eq21260 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19894 eq17573
    | exact resolve eq17573 eq19894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17573
  have eq21804 : x = (M.op x x) := by
    first
    | (have i₁ := eq17560 (M.op x x)
       have i₂ := eq17560 x
       grind)
    | exact superpose eq17560 eq17560
    | exact resolve eq17560 eq17560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17560
  have eq21882 : (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq18187
       have i₂ := eq21804
       grind)
    | exact superpose eq21804 eq18187
    | exact resolve eq18187 eq21804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18187
  have eq21949 : (k (σ y) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq17558
       have i₂ := eq21882
       grind)
    | exact superpose eq21882 eq17558
    | exact resolve eq17558 eq21882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17558
  have eq21960 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21260
       have i₂ := eq21882
       grind)
    | exact superpose eq21882 eq21260
    | exact resolve eq21260 eq21882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21260
  have eq21967 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21960
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq21960
    | exact resolve eq21960 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21960
  have eq21978 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21949
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq21949
    | exact resolve eq21949 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21949
  have eq21982 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21967
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21967
    | exact resolve eq21967 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21967
  have eq21983 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq21982
  have eq21991 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21978
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21978
    | exact resolve eq21978 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21978
  have eq22001 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq113 x
       have i₂ := eq21804
       grind)
    | exact superpose eq21804 eq113
    | exact resolve eq113 eq21804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq22036 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22001
       have i₂ := eq19893
       grind)
    | exact superpose eq19893 eq22001
    | exact resolve eq22001 eq19893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22001
  have eq22212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq22036 eq21983
    | exact resolve eq21983 eq22036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21983
  have eq22219 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq22212
       have r₂ := eq28
       grind)
    | exact resolve eq22212 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22212
  have eq22407 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq22219 eq21991
    | exact resolve eq21991 eq22219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21991 eq22219
  have eq22587 : (τ (σ (M.op x y))) = (k (τ (σ y)) (τ (σ (M.op x y)))) := by
    first
    | exact superpose eq22407 eq198
    | exact resolve eq198 eq22407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq22407
  have eq22590 : x = (k (τ (σ y)) x) := by
    first
    | exact superpose eq17556 eq22587
    | exact resolve eq22587 eq17556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17556 eq22587
  have eq22593 : x = (k y x) := by
    first
    | exact superpose eq40 eq22590
    | exact resolve eq22590 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq22590
  have eq22596 : x = (M.op y y) := by
    first
    | (have i₁ := eq22593
       have i₂ := eq21882
       grind)
    | exact superpose eq21882 eq22593
    | exact resolve eq22593 eq21882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21882 eq22593
  have eq23112 : y = (M.op x x) := by
    first
    | (have i₁ := eq17559 y
       have i₂ := eq22596
       grind)
    | exact superpose eq22596 eq17559
    | exact resolve eq17559 eq22596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17559 eq22596
  have eq23152 : x = y := by
    first
    | (have i₁ := eq23112
       have i₂ := eq21804
       grind)
    | exact superpose eq21804 eq23112
    | exact resolve eq23112 eq21804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21804 eq23112
  have eq23157 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq23152
       grind)
    | exact superpose eq23152 eq25
    | exact resolve eq25 eq23152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq23152
  have eq24158 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq23157
       have i₂ := eq19893
       grind)
    | exact superpose eq19893 eq23157
    | exact resolve eq23157 eq19893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19893 eq23157
  have eq24202 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24158 eq19894
    | exact resolve eq19894 eq24158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19894 eq24158
  have eq24893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22036 eq24202
    | exact resolve eq24202 eq22036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22036 eq24202
  have eq24995 : False := by grind
  exact eq24995

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_y_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq60
    | (have j0 := eq60 (σ X1) (σ X0)
       grind)
    | exact resolve eq60 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq60 (τ X0) X1
       grind)
    | exact superpose eq60 eq17
    | (have j1 := eq60 X1 (τ X0)
       grind)
    | exact resolve eq17 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq86 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq36 (τ X0)
       grind)
    | exact superpose eq36 eq18
    | exact resolve eq18 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq87 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq87
    | exact resolve eq87 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq110 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq23 X2 X0 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op (M.op X0 X1) X2) X0) = (M.op (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) X2) X0
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op x x) x) x
       have r₂ := eq24 x x x
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq169 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq194 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ X0) (σ X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq23
    | exact resolve eq23 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X0) X1
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq23
    | exact resolve eq23 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq642 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq612
    | (have j0 := eq612 X0 X1
       grind)
    | exact resolve eq612 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq733 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq169
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq169
    | (have j1 := eq60 (σ y) (σ x)
       grind)
    | exact resolve eq169 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq169
  have eq734 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq733
  have eq1425 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (k (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 (σ X0) (σ X0) x
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq124
    | exact resolve eq124 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq1435 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (k (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq4268 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 y x
       have i₂ := eq734
       grind)
    | exact superpose eq734 eq23
    | exact resolve eq23 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4269 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq23 y x X0
       have i₂ := eq734
       grind)
    | exact superpose eq734 eq23
    | exact resolve eq23 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq6622 : ∀ X0 X1 : G, (k (τ (M.op (σ (M.op X0 X0)) X1)) X0) = (τ (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ (M.op X0 X0)) X1) X0
       have i₂ := eq1435 X0 X1
       grind)
    | exact superpose eq1435 eq22
    | exact resolve eq22 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1435
  have eq22353 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op (σ (M.op X1 X1)) (M.op X0 (σ X1)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6622 X1 (M.op X0 (σ X1))
       have i₂ := eq110 (σ X1) (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq110 eq6622
    | exact resolve eq6622 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22853 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ (M.op x x)) (M.op (σ x) (σ y)))) x) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq22353 (σ y) x
       have i₂ := eq4269 X0
       grind)
    | exact superpose eq4269 eq22353
    | (have j1 := eq4269 X0
       grind)
    | exact resolve eq22353 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22854 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ (M.op x x)) (M.op (σ x) (σ y)))) x) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq22353 (σ y) x
       have i₂ := eq4268 X0
       grind)
    | exact superpose eq4268 eq22353
    | (have j1 := eq4268 X0
       grind)
    | exact resolve eq22353 eq4268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23107 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k (τ (σ x)) x) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq22854 X0
       have i₂ := eq195 x (σ y)
       grind)
    | exact superpose eq195 eq22854
    | (have j0 := eq22854 X0
       grind)
    | exact resolve eq22854 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22854
  have eq23108 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k (τ (σ x)) x) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq22853 X0
       have i₂ := eq195 x (σ y)
       grind)
    | exact superpose eq195 eq22853
    | (have j0 := eq22853 X0
       grind)
    | exact resolve eq22853 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22853
  have eq23195 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k x x) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq23107 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23107
    | (have j0 := eq23107 X0
       grind)
    | exact resolve eq23107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23107
  have eq23196 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (k x x) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq23108 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23108
    | (have j0 := eq23108 X0
       grind)
    | exact resolve eq23108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23108
  have eq23269 : ∀ X0 : G, (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq23195 X0
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq23195
    | (have j0 := eq23195 X0
       grind)
    | exact resolve eq23195 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23195
  have eq23270 : ∀ X0 : G, (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq23196 X0
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq23196
    | (have j0 := eq23196 X0
       grind)
    | exact resolve eq23196 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23196
  have eq23701 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq23269 X0
       grind)
    | exact superpose eq23269 eq11
    | (have j1 := eq23269 X0
       grind)
    | exact resolve eq11 eq23269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23269
  have eq24355 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq23270 X0
       grind)
    | exact superpose eq23270 eq11
    | (have j1 := eq23270 X0
       grind)
    | exact resolve eq11 eq23270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23270
  have eq24836 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (σ (M.op y y))) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq194 y (σ x)
       have i₂ := eq23701 X0
       grind)
    | exact superpose eq23701 eq194
    | (have j1 := eq23701 X0
       grind)
    | exact resolve eq194 eq23701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23701
  have eq25620 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (σ (M.op y y))) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq194 y (σ x)
       have i₂ := eq24355 X0
       grind)
    | exact superpose eq24355 eq194
    | (have j1 := eq24355 X0
       grind)
    | exact resolve eq194 eq24355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24355
  have eq54059 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (k (τ (σ y)) x) ∨ y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq6622 x (σ (M.op y y))
       have i₂ := eq24836 X0
       grind)
    | exact superpose eq24836 eq6622
    | (have j1 := eq24836 X0
       grind)
    | exact resolve eq6622 eq24836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24836
  have eq54150 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq54059 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq54059
    | (have j0 := eq54059 X0
       grind)
    | exact resolve eq54059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54059
  have eq56757 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (k (τ (σ y)) x) ∨ x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq6622 x (σ (M.op y y))
       have i₂ := eq25620 X0
       grind)
    | exact superpose eq25620 eq6622
    | (have j1 := eq25620 X0
       grind)
    | exact resolve eq6622 eq25620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6622 eq25620
  have eq56848 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq56757 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq56757
    | (have j0 := eq56757 X0
       grind)
    | exact resolve eq56757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56757
  have eq57226 : x = y ∨ (k y x) = (τ (M.op (σ y) (σ x))) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq54150 x
       have i₂ := eq56848 y
       grind)
    | exact superpose eq56848 eq54150
    | exact resolve eq54150 eq56848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54150 eq56848
  have eq57359 : x = y ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by grind
  clear eq57226
  have eq57715 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57359
       grind)
    | exact superpose eq57359 eq16
    | exact resolve eq16 eq57359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57359
  have eq57735 : (k y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have r₁ := eq57715
       have r₂ := eq99 x
       grind)
    | exact resolve eq57715 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57715
  have eq58193 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq57735
       have i₂ := eq4269 X0
       grind)
    | exact superpose eq4269 eq57735
    | (have j1 := eq4269 X0
       grind)
    | exact resolve eq57735 eq4269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4269
  have eq58194 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq57735
       have i₂ := eq4268 X0
       grind)
    | exact superpose eq4268 eq57735
    | (have j1 := eq4268 X0
       grind)
    | exact resolve eq57735 eq4268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4268
  have eq58200 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ y) (σ x))
       have i₂ := eq57735
       grind)
    | exact superpose eq57735 eq11
    | exact resolve eq11 eq57735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57735
  have eq58815 : (σ y) = (M.op (σ (M.op y y)) (σ (k y x))) := by
    first
    | (have i₁ := eq195 y (σ x)
       have i₂ := eq58200
       grind)
    | exact superpose eq58200 eq195
    | exact resolve eq195 eq58200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58826 : (σ x) = (M.op (σ (k y x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq194 x (σ y)
       have i₂ := eq58200
       grind)
    | exact superpose eq58200 eq194
    | exact resolve eq194 eq58200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq58200
  have eq59687 : (σ (k y x)) = (M.op (σ (M.op (k y x) (k y x))) (σ x)) := by
    first
    | (have i₁ := eq195 (k y x) (σ (M.op x x))
       have i₂ := eq58826
       grind)
    | exact superpose eq58826 eq195
    | exact resolve eq195 eq58826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq58826
  have eq69566 : x = y ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq58193 y
       have i₂ := eq58194 x
       grind)
    | exact superpose eq58194 eq58193
    | exact resolve eq58193 eq58194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58193 eq58194
  have eq69697 : x = y ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq69566
  have eq70144 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69697
       grind)
    | exact superpose eq69697 eq16
    | exact resolve eq16 eq69697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69697
  have eq70199 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq70144
       have r₂ := eq99 x
       grind)
    | exact resolve eq70144 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq70144
  have eq70640 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq70199
       grind)
    | exact superpose eq70199 eq11
    | exact resolve eq11 eq70199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71248 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70640
       grind)
    | exact superpose eq70640 eq16
    | exact resolve eq16 eq70640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71281 : (τ (σ (k y x))) = (k (τ (M.op (σ (M.op y y)) (σ (k y x)))) y) := by
    first
    | (have i₁ := eq22353 (σ x) y
       have i₂ := eq70640
       grind)
    | exact superpose eq70640 eq22353
    | exact resolve eq22353 eq70640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22353 eq70640
  have eq71352 : (τ (σ (k y x))) = (k (τ (σ y)) y) := by
    first
    | (have i₁ := eq71281
       have i₂ := eq58815
       grind)
    | exact superpose eq58815 eq71281
    | exact resolve eq71281 eq58815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58815 eq71281
  have eq71369 : (τ (σ (k y x))) = (k y y) := by
    first
    | (have i₁ := eq71352
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq71352
    | exact resolve eq71352 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71352
  have eq71375 : (M.op y y) = (τ (σ (k y x))) := by
    first
    | (have i₁ := eq71369
       have i₂ := eq36 y
       grind)
    | exact superpose eq36 eq71369
    | exact resolve eq71369 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq71369
  have eq71377 : (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq71375
       have i₂ := eq10 (k y x)
       grind)
    | exact superpose eq10 eq71375
    | exact resolve eq71375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71375
  have eq71834 : (σ (M.op y y)) = (M.op (σ (M.op (M.op y y) (M.op y y))) (σ x)) := by
    first
    | (have i₁ := eq59687
       have i₂ := eq71377
       grind)
    | exact superpose eq71377 eq59687
    | exact resolve eq59687 eq71377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59687
  have eq71902 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq71834
       have i₂ := eq23 y y y
       grind)
    | (have i₁ := eq71834
       have i₂ := eq23 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq23 eq71834
    | exact resolve eq71834 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71834
  have eq72349 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
    first
    | (have i₁ := eq71248
       have i₂ := eq71377
       grind)
    | exact superpose eq71377 eq71248
    | exact resolve eq71248 eq71377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71248
  have eq73697 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq199 y (σ x)
       have i₂ := eq71902
       grind)
    | exact superpose eq71902 eq199
    | (have j0 := eq199 y (σ x)
       grind)
    | (have r₁ := eq199 y (σ x)
       have r₂ := eq71902
       grind)
    | exact resolve eq199 eq71902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq71902
  have eq73766 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq73697
  have eq73788 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq73766
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq73766
    | exact resolve eq73766 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73766
  have eq74112 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq70199
       have i₂ := eq73788
       grind)
    | exact superpose eq73788 eq70199
    | exact resolve eq70199 eq73788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70199 eq73788
  have eq74225 : (k x y) = (k y x) := by
    first
    | (have i₁ := eq74112
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq74112
    | exact resolve eq74112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74112
  have eq74238 : (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq74225
       have i₂ := eq71377
       grind)
    | exact superpose eq71377 eq74225
    | exact resolve eq74225 eq71377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71377 eq74225
  have eq74540 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq642 x y
       have i₂ := eq74238
       grind)
    | exact superpose eq74238 eq642
    | (have j0 := eq642 y x
       grind)
    | exact resolve eq642 eq74238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq74238
  have eq74577 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq74540
       have r₂ := eq72349
       grind)
    | exact resolve eq74540 eq72349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74540
  have eq74869 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 y x
       have i₂ := eq74577
       grind)
    | exact superpose eq74577 eq23
    | exact resolve eq23 eq74577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq74577
  have eq75499 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq110 y (M.op x y) x
       have i₂ := eq74869 x
       grind)
    | exact superpose eq74869 eq110
    | exact resolve eq110 eq74869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq74869
  have eq75633 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq72349
       have i₂ := eq75499
       grind)
    | exact superpose eq75499 eq72349
    | exact resolve eq72349 eq75499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72349 eq75499
  have eq75744 : False := by grind
  exact eq75744

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq24 X2 X0 x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21
    | exact resolve eq21 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq83 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq24 X0 X0 X0
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0 X0
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq49
    | exact resolve eq49 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq15
    | exact resolve eq15 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq84 (σ X0)
       grind)
    | exact superpose eq84 eq92
    | exact resolve eq92 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq84 (τ X0)
       grind)
    | exact superpose eq84 eq91
    | exact resolve eq91 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
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
       have j1 := eq14 X0 X1
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
  have eq132 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq148 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (M.op X0 X1) X1
       have i₂ := eq30 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq30 eq83
    | (have j0 := eq83 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq83 (M.op x X0) X0
       have r₂ := eq30 X0 (M.op x X0) x
       grind)
    | exact resolve eq83 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 (M.op X0 X1)
       have i₂ := eq24 X0 X0 X1
       grind)
    | exact superpose eq24 eq83
    | (have j0 := eq83 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq83 x (M.op x x)
       have r₂ := eq24 x x x
       grind)
    | exact resolve eq83 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq151 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq152 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq154 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq24 X0 X0 X1
       grind)
    | (have i₁ := eq151 X0 X1
       have i₂ := eq24 X0 (M.op (M.op X0 X0) (M.op X0 X1)) x
       grind)
    | exact superpose eq24 eq151
    | exact resolve eq151 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq155 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 X1
       have i₂ := eq30 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq30 eq152
    | exact resolve eq152 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq167 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X1)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op X0 X0) (M.op X0 X1)
       have i₂ := eq154 X0 X1
       grind)
    | exact superpose eq154 eq49
    | exact resolve eq49 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X1) (M.op X0 X0)
       have i₂ := eq154 X0 X1
       grind)
    | exact superpose eq154 eq15
    | exact resolve eq15 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq170 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq168
    | exact resolve eq168 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq171 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X1)) (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq167
    | exact resolve eq167 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq167
  have eq195 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (σ (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq15
    | exact resolve eq15 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq196 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq93 (M.op X0 X1)
       grind)
    | exact superpose eq93 eq195
    | exact resolve eq195 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq205 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq170 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq170
    | exact resolve eq170 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq270 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq171 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq171
    | exact resolve eq171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq545 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (k X0 (M.op (σ (M.op X1 (τ X0))) (σ (M.op X1 (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq196
    | exact resolve eq196 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq620 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq132 X1 X0
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq132 X0 X1
       grind)
    | exact superpose eq132 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq132 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq132 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq132 X0 X1
       grind)
    | exact resolve eq13 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq684 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq652 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq652 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq652 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq652 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq1330 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq684 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq1332 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1330 X0 X1
       have j1 := eq132 X1 X0
       grind)
    | (have r₁ := eq1330 X0 X1
       have r₂ := eq132 X0 X1
       grind)
    | (have r₁ := eq1330 X1 X0
       have r₂ := eq132 X0 X1
       grind)
    | exact resolve eq1330 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1330
  have eq1416 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq1332 X1 X0
       grind)
    | exact superpose eq1332 eq49
    | (have j1 := eq1332 X1 X0
       grind)
    | exact resolve eq49 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1417 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1332 X1 X0
       grind)
    | exact superpose eq1332 eq15
    | (have j1 := eq1332 X1 X0
       grind)
    | exact resolve eq15 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1422 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (σ (M.op (τ X0) X1)) = (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq1332 (σ (M.op (τ X0) X1)) (M.op X0 X0)
       grind)
    | exact superpose eq1332 eq205
    | (have j1 := eq1332 (σ (M.op (τ X0) X1)) (M.op X0 X0)
       grind)
    | exact resolve eq205 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1434 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq1332 (τ (M.op (σ X0) X1)) (M.op X0 X0)
       grind)
    | exact superpose eq1332 eq270
    | (have j1 := eq1332 (τ (M.op (σ X0) X1)) (M.op X0 X0)
       grind)
    | exact resolve eq270 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1445 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1458 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = X0 ∨ (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1434 X0 X1
       have i₂ := eq270 X0 X1
       grind)
    | exact superpose eq270 eq1434
    | (have j0 := eq1434 X0 X1
       grind)
    | exact resolve eq1434 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq1434
  have eq1470 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = X0 ∨ (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1422 X0 X1
       have i₂ := eq205 X0 X1
       grind)
    | exact superpose eq205 eq1422
    | (have j0 := eq1422 X0 X1
       grind)
    | exact resolve eq1422 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq1422
  have eq1637 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (k X1 (M.op X2 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1445 X1 (M.op X2 (M.op X0 X1))
       have i₂ := eq30 X1 X2 X0
       grind)
    | exact superpose eq30 eq1445
    | (have j0 := eq1445 X1 X0
       grind)
    | exact resolve eq1445 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1768 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1417 x y
       grind)
    | exact superpose eq1417 eq16
    | (have j1 := eq1417 x y
       grind)
    | exact resolve eq16 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1851 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1768
       have i₂ := eq1332 (σ y) (σ x)
       grind)
    | exact superpose eq1332 eq1768
    | (have j1 := eq1332 y x
       grind)
    | (have r₁ := eq1768
       have r₂ := eq1332 (σ y) (σ x)
       grind)
    | exact resolve eq1768 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq1768
  have eq1853 : y = (k y x) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq1851
  have eq1863 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq1853
       grind)
    | exact superpose eq1853 eq15
    | exact resolve eq15 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq1864 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq1863
  have eq2008 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq49 (σ x) (σ y)
       have i₂ := eq1864
       grind)
    | exact superpose eq1864 eq49
    | exact resolve eq49 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq2010 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | (have i₁ := eq2008
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2008
    | exact resolve eq2008 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2011 : y = (k y x) := by
    first
    | (have i₁ := eq2010
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2010
    | exact resolve eq2010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2784 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq1458 X0 X1
       grind)
    | exact superpose eq1458 eq11
    | (have j1 := eq1458 X0 X1
       grind)
    | exact resolve eq11 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq2859 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq1470 X0 X1
       grind)
    | exact superpose eq1470 eq10
    | (have j1 := eq1470 X0 X1
       grind)
    | exact resolve eq10 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq2973 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (τ (M.op (σ X0) X1))) = X0 ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (τ (M.op (σ X0) X1)) X1 (M.op X0 X0)
       have i₂ := eq2784 X0 X1
       grind)
    | exact superpose eq2784 eq30
    | (have j1 := eq2784 X0 X1
       grind)
    | exact resolve eq30 eq2784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq3081 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (σ (M.op (τ X0) X1)) X1 (M.op X0 X0)
       have i₂ := eq2859 X0 X1
       grind)
    | exact superpose eq2859 eq30
    | (have j1 := eq2859 X0 X1
       grind)
    | exact resolve eq30 eq2859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq3324 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X2))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2973 (τ X0) X2 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2973
    | (have j0 := eq2973 (τ X0) X2 X2
       grind)
    | exact resolve eq2973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2973
  have eq3420 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X2))) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3324 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3324
    | (have j0 := eq3324 X0 X1 X2
       grind)
    | exact resolve eq3324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq3643 : ∀ X0 X2 X3 : G, (τ (M.op X0 X2)) = (M.op (τ X0) (M.op (τ (M.op X0 X2)) X3)) ∨ (M.op X0 X2) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq24 (M.op x (τ X0)) (τ (M.op X0 X2)) X3
       have i₂ := eq3420 X0 x X2
       grind)
    | exact superpose eq3420 eq24
    | (have j1 := eq3420 X0 x X2
       grind)
    | exact resolve eq24 eq3420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420
  have eq3809 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X2))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3081 (σ X0) X2 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3081
    | (have j0 := eq3081 (σ X0) X2 X2
       grind)
    | exact resolve eq3081 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081
  have eq3904 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X2))) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3809 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3809
    | (have j0 := eq3809 X0 X1 X2
       grind)
    | exact resolve eq3809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809
  have eq3976 : ∀ X0 X2 X3 : G, (σ (M.op X0 X2)) = (M.op (σ X0) (M.op (σ (M.op X0 X2)) X3)) ∨ (M.op X0 X2) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq24 (M.op x (σ X0)) (σ (M.op X0 X2)) X3
       have i₂ := eq3904 X0 x X2
       grind)
    | exact superpose eq3904 eq24
    | (have j1 := eq3904 X0 x X2
       grind)
    | exact resolve eq24 eq3904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904
  have eq6709 : ∀ X0 X1 X2 X3 : G, (τ X0) = (M.op (τ (M.op X1 X0)) (M.op (τ X0) X3)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3643 (M.op X0 x) (M.op x x) X3
       have i₂ := eq24 X0 x x
       grind)
    | exact superpose eq24 eq3643
    | (have j0 := eq3643 (M.op X1 X0) (M.op X0 X2) X3
       grind)
    | exact resolve eq3643 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643
  have eq6814 : ∀ X0 X1 X3 : G, (τ X0) = (M.op (τ (M.op X1 X0)) (M.op (τ X0) X3)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6709 X0 X1 x X3
       have i₂ := eq24 X1 X0 x
       grind)
    | (have i₁ := eq6709 X0 X1 x X3
       have i₂ := eq24 X0 (M.op (M.op X1 X0) (M.op X0 x)) x
       grind)
    | exact superpose eq24 eq6709
    | (have j0 := eq6709 X0 X1 x X3
       grind)
    | exact resolve eq6709 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6709
  have eq6856 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X1 (σ X0))) (M.op X0 X2)) = X0 ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6814 (σ X0) X1 x
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6814
    | (have j0 := eq6814 (σ X0) X1 x
       grind)
    | exact resolve eq6814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6814
  have eq6989 : ∀ X0 X1 X2 : G, (M.op (k (τ (σ X0)) (τ X1)) (M.op X0 X2)) = X0 ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6856 X0 X1 X2
       have i₂ := eq1416 X1 (σ X0)
       grind)
    | exact superpose eq1416 eq6856
    | (have j0 := eq6856 X0 X1 X2
       have j1 := eq1416 X1 (σ X0)
       grind)
    | exact resolve eq6856 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416 eq6856
  have eq7124 : ∀ X0 X1 X2 : G, (M.op (k (τ (σ X0)) (τ X1)) (M.op X0 X2)) = X0 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6989 X0 X1 X2
       have j1 := eq1445 (σ X0) X1
       grind)
    | (have r₁ := eq6989 X0 X1 X2
       have r₂ := eq1445 (σ X0) X1
       grind)
    | exact resolve eq6989 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445 eq6989
  have eq7138 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) X1) ∨ (M.op (k X0 (τ X1)) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7124 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7124
    | (have j0 := eq7124 X0 X1 X2
       grind)
    | exact resolve eq7124 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7124
  have eq7199 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ X0)) (τ X1)) ∨ (M.op (k X0 (τ X1)) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 (σ X0)
       have i₂ := eq7138 X0 X1 X2
       grind)
    | exact superpose eq7138 eq49
    | (have j1 := eq7138 X0 X1 X2
       grind)
    | exact resolve eq49 eq7138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq7138
  have eq7215 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (M.op (k X0 (τ X1)) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7199 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7199
    | (have j0 := eq7199 X0 X1 X2
       grind)
    | exact resolve eq7199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7199
  have eq7329 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op (k X1 (τ (σ X0))) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7215 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7215
    | (have j0 := eq7215 X1 (σ X0) X2
       grind)
    | exact resolve eq7215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7215
  have eq7395 : ∀ X0 X1 X2 : G, (M.op (k X1 X0) (M.op X1 X2)) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7329 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7329
    | (have j0 := eq7329 X0 X1 X2
       grind)
    | exact resolve eq7329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7329
  have eq7427 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (τ X1))) (M.op X1 X2)) = X1 ∨ (k X1 (M.op (σ (M.op X0 (τ X1))) (σ (M.op X0 (τ X1))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7395 (M.op (σ (M.op X0 (τ X1))) (σ (M.op X0 (τ X1)))) X1 X2
       have i₂ := eq545 X1 X0
       grind)
    | exact superpose eq545 eq7395
    | (have j0 := eq7395 (M.op (σ (M.op X0 (τ X1))) (σ (M.op X0 (τ X1)))) X1 X2
       grind)
    | exact resolve eq7395 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7395
  have eq7639 : ∀ X0 X1 X2 : G, (σ (M.op X0 (τ X1))) = X1 ∨ (M.op (σ (M.op X0 (τ X1))) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7427 X0 X1 X2
       have i₂ := eq545 X1 X0
       grind)
    | exact superpose eq545 eq7427
    | (have j0 := eq7427 X0 X1 X2
       grind)
    | exact resolve eq7427 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq7427
  have eq8541 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq7639 X1 X0 X2
       grind)
    | exact superpose eq7639 eq10
    | (have j1 := eq7639 X1 X0 X2
       grind)
    | exact resolve eq10 eq7639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7639
  have eq9009 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) ∨ (τ (σ X0)) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8541 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8541
    | (have j0 := eq8541 (σ X0) X1 X2
       grind)
    | exact resolve eq8541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8541
  have eq9182 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9009 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9009
    | (have j0 := eq9009 X0 X1 X2
       grind)
    | exact resolve eq9009 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9009
  have eq10159 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3976 X1 X0 (M.op (σ X0) x)
       have i₂ := eq9182 X0 X1 x
       grind)
    | exact superpose eq9182 eq3976
    | (have j0 := eq3976 X1 X0 x
       have j1 := eq9182 X0 X1 x
       grind)
    | exact resolve eq3976 eq9182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9182
  have eq16459 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10159 y x
       grind)
    | exact superpose eq10159 eq16
    | (have j1 := eq10159 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq10159 y x
       grind)
    | exact resolve eq16 eq10159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10159
  have eq16524 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16459
  have eq16634 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq25 x y x
       have i₂ := eq16524
       grind)
    | exact superpose eq16524 eq25
    | exact resolve eq25 eq16524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq16657 : ∀ X0 : G, y ≠ y ∨ y = (k y (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1637 x y X0
       have i₂ := eq16524
       grind)
    | exact superpose eq16524 eq1637
    | (have j0 := eq1637 x y X0
       grind)
    | (have r₁ := eq1637 x y x
       have r₂ := eq16524
       grind)
    | exact resolve eq1637 eq16524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq16667 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3976 x y x
       have i₂ := eq16524
       grind)
    | exact superpose eq16524 eq3976
    | (have j0 := eq3976 x y x
       grind)
    | exact resolve eq3976 eq16524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq16687 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq16667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16667
  have eq16693 : ∀ X0 : G, y = (k y (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq16657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16657
  have eq17078 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16693 X0
       have i₂ := eq16524
       grind)
    | exact superpose eq16524 eq16693
    | exact resolve eq16693 eq16524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16693
  have eq17117 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17078 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17078
  have eq17132 : y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17117 x
       have i₂ := eq16524
       grind)
    | exact superpose eq16524 eq17117
    | exact resolve eq17117 eq16524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16524 eq17117
  have eq17160 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq17132
  have eq17169 : x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17160
       have i₂ := eq84 y
       grind)
    | exact superpose eq84 eq17160
    | exact resolve eq17160 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq17160
  have eq17178 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq17169
       grind)
    | exact superpose eq17169 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq17169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17180 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq24 X0 x y
       have i₂ := eq17169
       grind)
    | exact superpose eq17169 eq24
    | exact resolve eq24 eq17169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17181 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq24 x y X0
       have i₂ := eq17169
       grind)
    | exact superpose eq17169 eq24
    | exact resolve eq24 eq17169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq17239 : y = (M.op x y) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17178
       have i₂ := eq2011
       grind)
    | exact superpose eq2011 eq17178
    | exact resolve eq17178 eq2011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011 eq17178
  have eq17240 : x = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17180 (M.op x x)
       have i₂ := eq17180 x
       grind)
    | exact superpose eq17180 eq17180
    | exact resolve eq17180 eq17180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17180
  have eq17318 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq17240
  have eq17486 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17181 y
       have i₂ := eq17318
       grind)
    | exact superpose eq17318 eq17181
    | exact resolve eq17181 eq17318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17181 eq17318
  have eq17561 : y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq17486
       have r₂ := eq17239
       grind)
    | exact resolve eq17486 eq17239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17239 eq17486
  have eq17574 : x = y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17169
       have i₂ := eq17561
       grind)
    | exact superpose eq17561 eq17169
    | exact resolve eq17169 eq17561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17169 eq17561
  have eq17632 : x = y ∨ y = (M.op y y) := by grind
  clear eq17574
  have eq17642 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17632
       grind)
    | exact superpose eq17632 eq16
    | exact resolve eq16 eq17632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17632
  have eq17689 : y = (M.op y y) := by
    first
    | (have r₁ := eq17642
       have r₂ := eq93 x
       grind)
    | exact resolve eq17642 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17642
  have eq17747 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq93 y
       have i₂ := eq17689
       grind)
    | exact superpose eq17689 eq93
    | exact resolve eq93 eq17689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq17793 : ∀ X0 : G, y = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq30 y x y
       have i₂ := eq17689
       grind)
    | exact superpose eq17689 eq30
    | exact resolve eq30 eq17689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq18042 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17793 x
       have i₂ := eq16634 X0
       grind)
    | exact superpose eq16634 eq17793
    | (have j1 := eq16634 X0
       grind)
    | exact resolve eq17793 eq16634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16634 eq17793
  have eq20895 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18042 y
       have i₂ := eq17689
       grind)
    | exact superpose eq17689 eq18042
    | exact resolve eq18042 eq17689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17689 eq18042
  have eq20952 : y = (M.op x y) := by grind
  clear eq20895
  have eq20957 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq16
    | exact resolve eq16 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20978 : ∀ X0 : G, x = y ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16687 X0
       have i₂ := eq20952
       grind)
    | exact superpose eq20952 eq16687
    | (have j0 := eq16687 X0
       grind)
    | exact resolve eq16687 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16687 eq20952
  have eq22315 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq17747
       have i₂ := eq20978 X0
       grind)
    | exact superpose eq20978 eq17747
    | (have j1 := eq20978 X0
       grind)
    | exact resolve eq17747 eq20978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22351 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq20957
       have i₂ := eq20978 X0
       grind)
    | exact superpose eq20978 eq20957
    | (have j1 := eq20978 X0
       grind)
    | exact resolve eq20957 eq20978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20978
  have eq22362 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq22315 X0
       have j1 := eq22351 X0
       grind)
    | (have r₁ := eq22315 X0
       have r₂ := eq22351 X0
       grind)
    | exact resolve eq22315 eq22351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22315 eq22351
  have eq22382 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22362 (σ y)
       have i₂ := eq17747
       grind)
    | exact superpose eq17747 eq22362
    | exact resolve eq22362 eq17747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17747 eq22362
  have eq22491 : False := by grind
  exact eq22491
