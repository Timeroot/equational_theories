import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyy_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
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
  clear eq36
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (M.op x (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
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
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op X1 X2) X0)) ≠ X0 ∨ (M.op X0 X3) = X0 ∨ (k (M.op X0 X3) (M.op (M.op X1 X2) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X0 X3) (M.op (M.op X1 X2) X0)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq12
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq114 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq114 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq115 (σ X0)
       grind)
    | exact superpose eq115 eq10
    | exact resolve eq10 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq43
    | exact resolve eq43 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq49
    | exact resolve eq49 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq120
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq120
    | exact resolve eq120 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq118
    | exact resolve eq118 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq124 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq117
    | exact resolve eq117 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq130 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq105
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq105
    | exact resolve eq105 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq131 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq130
    | exact resolve eq130 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq139 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
       have i₂ := eq115 sF1
       grind)
    | exact superpose eq115 eq141
    | exact resolve eq141 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq147 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq115 sF0
       grind)
    | exact superpose eq115 eq144
    | exact resolve eq144 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq156 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq139 eq16
    | exact resolve eq16 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq266 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq256 eq14
    | exact resolve eq14 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq336 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
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
  have eq371 : ∀ X0 : G, x ≠ (M.op (M.op x y) (M.op X0 x)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq332 eq12
    | exact resolve eq12 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq115 (τ X0)
       grind)
    | exact superpose eq115 eq34
    | exact resolve eq34 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq459 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq448 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq448
    | exact resolve eq448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq461 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq459 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq459
    | exact resolve eq459 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq507 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq550 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X2) X0
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) X0) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 (M.op x x) X0 x x
       have i₂ := eq52 X0 x x
       grind)
    | exact superpose eq52 eq112
    | (have j0 := eq112 (M.op X0 X1) X1 X2 X2
       grind)
    | (have r₁ := eq112 (M.op X1 X2) X1 X2 (M.op X1 X2)
       have r₂ := eq52 (M.op X1 X2) (M.op X1 X2) (M.op X1 X2)
       grind)
    | exact resolve eq112 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq750 : (σ (M.op (k x (M.op x y)) (k x (M.op x y)))) = (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq124
    | exact resolve eq124 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq766 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (σ X0) (σ X0)
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq52
    | exact resolve eq52 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X0) X1
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq52
    | exact resolve eq52 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X0) x
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq53
    | exact resolve eq53 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq842 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq860 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq842 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq865 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq844 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq844 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq844 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq867 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq860 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq860
    | (have j0 := eq860 X0 X1
       grind)
    | exact resolve eq860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq868 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq867 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq878 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq865 X0 X1
       have i₂ := eq124 X1
       grind)
    | exact superpose eq124 eq865
    | (have j0 := eq865 X0 X1
       grind)
    | exact resolve eq865 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq884 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq878 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq878
    | (have j0 := eq878 X0 X1
       grind)
    | exact resolve eq878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq896 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq452
    | exact resolve eq452 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq452 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq452
    | exact resolve eq452 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq907 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq452 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq452
    | (have j0 := eq452 X0 x
       grind)
    | exact resolve eq452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (k (τ X0) (k x x)) := by
    intro X0
    first
    | (have i₁ := eq899 X0
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq899
    | exact resolve eq899 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq928 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq925 X0
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq925
    | exact resolve eq925 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq1017 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq16
    | exact resolve eq16 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq20 eq507
    | (have j0 := eq507 (M.op x y) X0
       grind)
    | exact resolve eq507 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq1220 : (k (M.op x y) (k x x)) = (τ (k (σ (M.op x y)) (k (σ x) (σ x)))) := by
    first
    | exact superpose eq49 eq1057
    | exact resolve eq1057 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1233 : (k (M.op x y) (k x x)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq1220
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq1220
    | exact resolve eq1220 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1236 : (k (M.op x y) (M.op x x)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq1233
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq1233
    | exact resolve eq1233 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1233
  have eq1293 : (M.op (k x (M.op x y)) (k x (M.op x y))) = (τ (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y))))) := by
    first
    | exact superpose eq64 eq1017
    | exact resolve eq1017 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1479 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op X1 (τ (M.op X0 X0))) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 (τ X0) X1 (τ X0)
       have i₂ := eq1017 X0
       grind)
    | exact superpose eq1017 eq336
    | exact resolve eq336 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq1017
  have eq4666 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ (M.op X0 X0)) X1) ∨ (σ (M.op X0 X0)) = (k (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq550 (σ X0) (σ X0) x
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq550
    | exact resolve eq550 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq8447 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq868 X0 X1
       have j1 := eq858 X1 X0
       grind)
    | (have r₁ := eq868 X1 X0
       have r₂ := eq858 X0 X1
       grind)
    | (have r₁ := eq868 X0 X0
       have r₂ := eq858 X0 X0
       grind)
    | exact resolve eq868 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq868
  have eq8454 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8447 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8447
    | exact resolve eq8447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8531 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq8447 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8447
    | (have j0 := eq8447 x X0
       grind)
    | exact resolve eq8447 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8532 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8447 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8447
    | (have j0 := eq8447 y X0
       grind)
    | exact resolve eq8447 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8533 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq8447
    | (have j0 := eq8447 (M.op x y) X0
       grind)
    | exact resolve eq8447 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8642 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 (σ X0) (σ X1)
       have i₂ := eq8447 X0 X1
       grind)
    | exact superpose eq8447 eq52
    | (have j1 := eq8447 X0 X1
       grind)
    | exact resolve eq52 eq8447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8643 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ X0) (σ X1) X2
       have i₂ := eq8447 X0 X1
       grind)
    | exact superpose eq8447 eq52
    | (have j1 := eq8447 X0 X1
       grind)
    | exact resolve eq52 eq8447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8447
  have eq8687 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8454 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq8454
    | (have j0 := eq8454 X0 X1
       grind)
    | exact resolve eq8454 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8454
  have eq9355 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ X0 ∨ (σ (k (τ X0) X1)) = (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq884 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq884
    | (have j0 := eq884 (τ X0) X1
       grind)
    | exact resolve eq884 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq9537 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) ≠ X0 ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9355 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9355
    | (have j0 := eq9355 X0 X1
       grind)
    | exact resolve eq9355 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9355
  have eq9548 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ X0 ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9537 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9537
    | (have j0 := eq9537 X0 X1
       grind)
    | exact resolve eq9537 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq9537
  have eq11839 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) ∨ (σ (M.op X0 X0)) = (k (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq719 (σ X0) (σ X0) x
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq719
    | exact resolve eq719 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq719
  have eq18525 : (τ (σ (M.op x y))) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq92 eq60
    | exact resolve eq60 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18540 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq18525
    | exact resolve eq18525 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18525
  have eq22972 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8531 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8531
    | (have j0 := eq8531 y
       grind)
    | exact resolve eq8531 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22973 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq8531
    | (have j0 := eq8531 (M.op x y)
       grind)
    | exact resolve eq8531 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8531
  have eq23028 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq45 eq22973
    | exact resolve eq22973 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22973
  have eq23029 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq22972
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq22972
    | exact resolve eq22972 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq22972
  have eq23046 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq23029
    | exact resolve eq23029 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23029
  have eq23140 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8532 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8532
    | (have j0 := eq8532 x
       grind)
    | exact resolve eq8532 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8532
  have eq23199 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23140
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq23140
    | exact resolve eq23140 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq23140
  have eq23216 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23199
    | exact resolve eq23199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23199
  have eq23232 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq8533 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8533
    | exact resolve eq8533 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23309 : (M.op (σ (M.op x y)) (σ x)) = (σ (k (M.op x y) x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq8533 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8533
    | (have j0 := eq8533 x
       grind)
    | exact resolve eq8533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8533
  have eq23366 : (M.op (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq139 eq23309
    | exact resolve eq23309 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23309
  have eq23377 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq23232 X0
       have i₂ := eq38 X0 sF0
       grind)
    | exact superpose eq38 eq23232
    | (have j0 := eq23232 X0
       grind)
    | exact resolve eq23232 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq23232
  have eq23384 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq23377
    | (have j0 := eq23377 X0
       grind)
    | exact resolve eq23377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23377
  have eq23494 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq8687 X0 X1
       grind)
    | exact superpose eq8687 eq452
    | (have j1 := eq8687 X0 X1
       grind)
    | exact resolve eq452 eq8687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq8687
  have eq203982 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op X2 (σ (τ X0))) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8642 (τ X0) (τ X1) X2
       have i₂ := eq896 X1 X0
       grind)
    | exact superpose eq896 eq8642
    | (have j0 := eq8642 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq8642 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8642
  have eq205176 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op X2 (σ (τ X0))) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq203982 X0 X1 X2
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq203982
    | (have j0 := eq203982 X0 X1 X2
       grind)
    | exact resolve eq203982 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203982
  have eq205577 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq205176 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq205176
    | (have j0 := eq205176 X0 X1 X2
       grind)
    | exact resolve eq205176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205176
  have eq205885 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op (M.op X2 X0) (k X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq205577 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq205577
    | (have j0 := eq205577 X0 X1 X2
       grind)
    | exact resolve eq205577 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205577
  have eq205974 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X0 X1)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq205885 X0 X1 X2
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq205885
    | (have j0 := eq205885 X0 X1 X2
       grind)
    | exact resolve eq205885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205885
  have eq206653 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X1)) X2)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8643 (τ X0) (τ X1) X2
       have i₂ := eq896 X1 X0
       grind)
    | exact superpose eq896 eq8643
    | (have j0 := eq8643 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq8643 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq8643
  have eq208212 : ∀ X0 X1 X2 : G, (M.op (σ (τ (k X0 X1))) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206653 X0 X0 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq206653
    | (have j0 := eq206653 X0 X1 X2
       grind)
    | exact resolve eq206653 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206653
  have eq208616 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208212 X0 X1 X2
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq208212
    | (have j0 := eq208212 X0 X1 X2
       grind)
    | exact resolve eq208212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208212
  have eq208920 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op (k X0 X1) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208616 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq208616
    | (have j0 := eq208616 X0 X1 X2
       grind)
    | exact resolve eq208616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208616
  have eq209003 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq208920 X0 X1 X2
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq208920
    | (have j0 := eq208920 X0 X1 X2
       grind)
    | exact resolve eq208920 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208920
  have eq457501 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (σ (M.op (τ X0) (τ X0))) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9548 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9548
    | exact resolve eq9548 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9548
  have eq457951 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq457501 X0 X1
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq457501
    | (have j0 := eq457501 X0 X1
       grind)
    | exact resolve eq457501 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457501
  have eq858061 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (k (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq11839 X0 X1
       have j1 := eq4666 X0 X1
       grind)
    | (have r₁ := eq11839 X0 X1
       have r₂ := eq4666 X0 X1
       grind)
    | exact resolve eq11839 eq4666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666 eq11839
  have eq860607 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) ≠ (M.op (M.op (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) X1) (M.op X0 X0)) ∨ (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (k (M.op (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq858061 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq858061
    | exact resolve eq858061 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq858061
  have eq861341 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (M.op (M.op (σ (τ X0)) X1) (M.op X0 X0)) ∨ (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (k (M.op (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq860607 X0 X1
       have i₂ := eq52 (τ X0) (τ X0) (τ X0)
       grind)
    | (have i₁ := eq860607 X0 X1
       have i₂ := eq52 X0 (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) x
       grind)
    | exact superpose eq52 eq860607
    | (have j0 := eq860607 X0 X1
       grind)
    | exact resolve eq860607 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860607
  have eq861534 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X0 ∨ (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (k (M.op (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq861341 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq861341
    | (have j0 := eq861341 X0 X1
       grind)
    | exact resolve eq861341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861341
  have eq861610 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op (σ (τ X0)) X1) (M.op X0 X0)) ∨ (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq861534 X0 X1
       have i₂ := eq52 (τ X0) (τ X0) (τ X0)
       grind)
    | (have i₁ := eq861534 X0 X1
       have i₂ := eq52 X0 (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) x
       grind)
    | exact superpose eq52 eq861534
    | (have j0 := eq861534 X0 X1
       grind)
    | (have r₁ := eq861534 x x
       have r₂ := eq52 x x x
       grind)
    | exact resolve eq861534 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861534
  have eq861650 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq861610 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq861610
    | (have j0 := eq861610 X0 X1
       grind)
    | exact resolve eq861610 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861610
  have eq2151883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq23046 eq92
    | exact resolve eq92 eq23046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq23046
  have eq2151938 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq2151883
       have r₂ := eq27
       grind)
    | exact resolve eq2151883 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151883
  have eq2151952 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2151938 eq334
    | exact resolve eq334 eq2151938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2151977 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2151938 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2151938
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2151938
       grind)
    | exact resolve eq13 eq2151938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2151983 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2151938 eq52
    | exact resolve eq52 eq2151938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151938
  have eq2152058 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq2151977
  have eq2152933 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2151952 eq2151983
    | exact resolve eq2151983 eq2151952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151952 eq2151983
  have eq2153222 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq2152933
  have eq2153385 : (τ (σ x)) = (M.op x x) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2153222 eq121
    | exact resolve eq121 eq2153222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153222
  have eq2155069 : (M.op x y) = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq2153385
    | exact resolve eq2153385 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153385
  have eq2155184 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq332 y
       have i₂ := eq2155069
       grind)
    | exact superpose eq2155069 eq332
    | exact resolve eq332 eq2155069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155069
  have eq2157597 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2155184 eq147
    | exact resolve eq147 eq2155184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155184
  have eq2157831 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2157597
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2157597
    | exact resolve eq2157597 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157597
  have eq2683416 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2152058 eq60
    | exact resolve eq60 eq2152058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq2152058
  have eq2683498 : (k x y) = (M.op y y) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq131 eq2683416
    | exact resolve eq2683416 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq2683416
  have eq2683502 : (k x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq2683498
       have r₂ := eq13 x y
       grind)
    | exact resolve eq2683498 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683498
  have eq2683553 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq18540
       have i₂ := eq2683502
       grind)
    | exact superpose eq2683502 eq18540
    | exact resolve eq18540 eq2683502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18540 eq2683502
  have eq2683646 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by grind
  clear eq2683553
  have eq2691791 : (M.op x y) = (M.op y x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq320 y
       have i₂ := eq2683646
       grind)
    | exact superpose eq2683646 eq320
    | exact resolve eq320 eq2683646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683646
  have eq2698336 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq320 x
       have i₂ := eq2691791
       grind)
    | exact superpose eq2691791 eq320
    | exact resolve eq320 eq2691791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2691791
  have eq2698462 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y x) := by grind
  clear eq2698336
  have eq2699310 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2698462 eq50
    | exact resolve eq50 eq2698462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2699344 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2698462 eq766
    | exact resolve eq766 eq2698462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq2699345 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2698462 eq767
    | exact resolve eq767 eq2698462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq2698462
  have eq2699504 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20 eq2699345
    | (have j0 := eq2699345 X0
       grind)
    | exact resolve eq2699345 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699345
  have eq2699505 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2699344 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2699344
    | (have j0 := eq2699344 X0
       grind)
    | exact resolve eq2699344 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699344
  have eq2699586 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2699504 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2699504
    | (have j0 := eq2699504 X0
       grind)
    | exact resolve eq2699504 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699504
  have eq2699587 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20 eq2699505
    | (have j0 := eq2699505 X0
       grind)
    | exact resolve eq2699505 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699505
  have eq2705321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2157831 eq2699587
    | exact resolve eq2699587 eq2157831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157831
  have eq2705449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq2705321
  have eq2705457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq2705449
    | exact resolve eq2705449 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705449
  have eq2705458 : x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2705457
       have r₂ := eq27
       grind)
    | exact resolve eq2705457 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705457
  have eq2705472 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq332 y
       have i₂ := eq2705458
       grind)
    | exact superpose eq2705458 eq332
    | exact resolve eq332 eq2705458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2705504 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq2705458
       grind)
    | exact superpose eq2705458 eq52
    | exact resolve eq52 eq2705458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705458
  have eq2719741 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2705472 eq2705504
    | exact resolve eq2705504 eq2705472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705472 eq2705504
  have eq2720060 : x = (M.op x x) := by grind
  clear eq2719741
  have eq2720859 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq123
    | exact resolve eq123 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2721961 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq332 x
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq332
    | exact resolve eq332 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2721962 : x ≠ (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq371 x
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq371
    | exact resolve eq371 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq2721990 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq768 x x
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq768
    | exact resolve eq768 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq2722095 : ∀ X0 : G, x = (M.op (k X0 x) x) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq209003 X0 x x
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq209003
    | (have j0 := eq209003 x (k X0 x) x
       grind)
    | exact resolve eq209003 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209003
  have eq2722130 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq2721990 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2721990
    | (have j0 := eq2721990 X0
       grind)
    | exact resolve eq2721990 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721990
  have eq2722940 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2720859
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2720859
    | exact resolve eq2720859 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720859
  have eq2723018 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2721961 eq85
    | exact resolve eq85 eq2721961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq2723044 : x ≠ (M.op x y) ∨ (M.op x x) = (k (M.op x y) x) := by
    first
    | exact superpose eq2721961 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | exact resolve eq13 eq2721961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2723122 : ∀ X0 : G, (M.op x y) = (M.op x (k (M.op x y) X0)) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2721961 eq205974
    | (have j0 := eq205974 (M.op x y) X0 x
       grind)
    | exact resolve eq205974 eq2721961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2723134 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq2723018
  have eq2723137 : x ≠ (M.op x y) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq2723044
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq2723044
    | exact resolve eq2723044 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723044
  have eq2723142 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2723134
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2723134
    | exact resolve eq2723134 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723134
  have eq2724979 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2722940 eq334
    | exact resolve eq334 eq2722940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq2744270 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq23028 eq2723142
    | exact resolve eq2723142 eq23028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2744277 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2723142 eq64
    | exact resolve eq64 eq2723142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2744284 : (τ (M.op (σ x) (σ x))) = (M.op (k x (M.op x y)) (k x (M.op x y))) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2723142 eq1293
    | exact resolve eq1293 eq2723142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq2723142
  have eq2744351 : (M.op x x) = (M.op (k x (M.op x y)) (k x (M.op x y))) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq121 eq2744284
    | exact resolve eq2744284 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744284
  have eq2744358 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq28 eq2744277
    | exact resolve eq2744277 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744277
  have eq2744363 : x = (M.op (k x (M.op x y)) (k x (M.op x y))) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2744351
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq2744351
    | exact resolve eq2744351 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744351
  have eq2752904 : ∀ X0 : G, x = (M.op (τ (k X0 (σ x))) x) ∨ (τ X0) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2722095 (τ X0)
       have i₂ := eq907 X0
       grind)
    | exact superpose eq907 eq2722095
    | (have j0 := eq2722095 (τ X0)
       grind)
    | exact resolve eq2722095 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq2722095
  have eq2755002 : ∀ X0 : G, (M.op x y) = (M.op x (τ (k (σ (M.op x y)) X0))) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1057 eq2723122
    | (have j0 := eq2723122 (τ X0)
       grind)
    | exact resolve eq2723122 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq2723122
  have eq2767125 : x ≠ (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | (have r₁ := eq2721962
       have r₂ := eq2723137
       grind)
    | exact resolve eq2721962 eq2723137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721962 eq2723137
  have eq2797960 : ∀ X0 : G, (k x (M.op x y)) = (M.op (M.op X0 (k x (M.op x y))) x) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq2744363 eq52
    | exact resolve eq52 eq2744363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744363
  have eq2798375 : (M.op x y) = (M.op x (τ (M.op (σ (M.op x y)) (σ x)))) ∨ (M.op x y) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23366 eq2755002
    | (have j0 := eq2755002 (σ x)
       grind)
    | exact resolve eq2755002 eq23366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23366
  have eq2798383 : (M.op x y) = (M.op x (k (M.op x y) (M.op x x))) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ x))) (M.op x y)) := by
    first
    | exact superpose eq1236 eq2755002
    | (have j0 := eq2755002 (M.op (σ x) (σ x))
       grind)
    | exact resolve eq2755002 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq2755002
  have eq2798735 : (M.op x y) = (M.op x (k (M.op x y) x)) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ x))) (M.op x y)) := by
    first
    | (have i₁ := eq2798383
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq2798383
    | exact resolve eq2798383 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798383
  have eq2798743 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x (τ (M.op (σ (M.op x y)) (σ x)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq28 eq2798375
    | exact resolve eq2798375 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798375
  have eq2799014 : (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ (M.op x y) = (M.op x (k (M.op x y) x)) := by
    first
    | exact superpose eq121 eq2798735
    | exact resolve eq2798735 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq2798735
  have eq2799018 : (M.op x y) = (M.op x (τ (M.op (σ (M.op x y)) (σ x)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2721961 eq2798743
    | exact resolve eq2798743 eq2721961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798743
  have eq2799231 : (M.op x y) = (M.op x (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq332 eq2799014
    | exact resolve eq2799014 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq2799014
  have eq2799703 : ∀ X0 : G, (k (M.op x y) x) = (M.op (M.op x y) (M.op (k (M.op x y) x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2799231 eq52
    | exact resolve eq52 eq2799231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2827385 : x = (M.op (τ (M.op (σ y) (σ x))) x) ∨ (τ (σ y)) = (M.op x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23216 eq2752904
    | (have j0 := eq2752904 (σ y)
       grind)
    | exact resolve eq2752904 eq23216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23216
  have eq2827508 : x = (M.op (τ (M.op (σ (M.op x y)) (σ x))) x) ∨ (τ (σ (M.op x y))) = (M.op x (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23384 eq2752904
    | (have j0 := eq2752904 (σ (M.op x y))
       have j1 := eq23384 (σ x)
       grind)
    | exact resolve eq2752904 eq23384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23384 eq2752904
  have eq2827959 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (τ (M.op (σ (M.op x y)) (σ x))) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30 eq2827508
    | exact resolve eq2827508 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827508
  have eq2828081 : y = (M.op x y) ∨ x = (M.op (τ (M.op (σ y) (σ x))) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq2827385
    | exact resolve eq2827385 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2827385
  have eq2828279 : x = (M.op (τ (M.op (σ (M.op x y)) (σ x))) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2721961 eq2827959
    | exact resolve eq2827959 eq2721961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827959
  have eq2828378 : x = (M.op (τ (M.op (σ y) (σ x))) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2828081
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2828081
    | exact resolve eq2828081 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2828081
  have eq2831616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2744270 eq2699587
    | exact resolve eq2699587 eq2744270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744270
  have eq2831728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq26 eq2831616
    | exact resolve eq2831616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831616
  have eq2831739 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2831728
       have r₂ := eq27
       grind)
    | exact resolve eq2831728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831728
  have eq2835099 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2831739 eq2699586
    | exact resolve eq2699586 eq2831739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699586
  have eq2835232 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq2835099
  have eq2840308 : x = (M.op (τ (σ (M.op x y))) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2835232 eq2828378
    | exact resolve eq2828378 eq2835232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828378 eq2835232
  have eq2840480 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq30 eq2840308
    | exact resolve eq2840308 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840308
  have eq2840481 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq2840480
  have eq3078350 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2840481 eq266
    | exact resolve eq266 eq2840481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq3078367 : (M.op x y) = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2840481 eq2699310
    | exact resolve eq2699310 eq2840481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699310 eq2840481
  have eq3078492 : (M.op x y) = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3078367
  have eq3078531 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3078350
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq3078350
    | exact resolve eq3078350 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3078350
  have eq3107099 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (M.op X0 (M.op (σ x) (σ x)))) ∨ (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23494 X0 (M.op x x)
       have i₂ := eq123
       grind)
    | exact superpose eq123 eq23494
    | exact resolve eq23494 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23494
  have eq3109793 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (M.op X0 (σ x))) ∨ (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2722940 eq3107099
    | (have j0 := eq3107099 X0
       grind)
    | exact resolve eq3107099 eq2722940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107099
  have eq3110291 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (τ (M.op X0 (σ x))) ∨ (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3109793 X0
       have i₂ := eq928 X0
       grind)
    | exact superpose eq928 eq3109793
    | (have j0 := eq3109793 X0
       grind)
    | exact resolve eq3109793 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq3109793
  have eq3110719 : ∀ X0 : G, (τ (k X0 (σ x))) = (τ (M.op X0 (σ x))) ∨ (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2722940 eq3110291
    | (have j0 := eq3110291 X0
       grind)
    | exact resolve eq3110291 eq2722940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110291
  have eq3111034 : ∀ X0 : G, (τ (k X0 (σ x))) = (τ (M.op X0 (σ x))) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2722940 eq3110719
    | (have j0 := eq3110719 X0
       grind)
    | exact resolve eq3110719 eq2722940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110719
  have eq3112138 : (k (M.op x y) x) = (τ (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq156 eq3111034
    | (have j0 := eq3111034 (σ (M.op x y))
       grind)
    | exact resolve eq3111034 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq3111034
  have eq3115668 : (τ (σ x)) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2831739 eq3112138
    | exact resolve eq3112138 eq2831739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831739
  have eq3115672 : x = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3112138 eq2828279
    | exact resolve eq2828279 eq3112138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828279 eq3112138
  have eq3116236 : x = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq3115672
  have eq3116263 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq3115668
    | exact resolve eq3115668 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115668
  have eq3116271 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq3116263
       have r₂ := eq2767125
       grind)
    | exact resolve eq3116263 eq2767125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116263
  have eq3120467 : (M.op (M.op x y) x) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3116236 eq2799703
    | exact resolve eq2799703 eq3116236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799703 eq3116236
  have eq3120595 : (M.op (M.op x y) x) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq3120467
  have eq3120864 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (k (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3116271 eq2722130
    | exact resolve eq2722130 eq3116271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116271
  have eq3121124 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3120595 eq139
    | exact resolve eq139 eq3120595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq3120595
  have eq3121749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (k (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3120864 eq2699587
    | exact resolve eq2699587 eq3120864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699587 eq3120864
  have eq3121838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (k (M.op x y) x) := by grind
  clear eq3121749
  have eq3121857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq3121838
    | exact resolve eq3121838 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121838
  have eq3121870 : x = (k (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq3121857
       have r₂ := eq27
       grind)
    | exact resolve eq3121857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121857
  have eq3121959 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3121870 eq2799231
    | exact resolve eq2799231 eq3121870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121870
  have eq3122175 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3121959
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq3121959
    | exact resolve eq3121959 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121959
  have eq3122176 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq3122175
  have eq3122573 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq320 x
       have i₂ := eq3122176
       grind)
    | exact superpose eq3122176 eq320
    | exact resolve eq320 eq3122176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122176
  have eq4951240 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3078492
  have eq4951281 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4951240
       have r₂ := eq3078531
       grind)
    | exact resolve eq4951240 eq3078531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3078531 eq4951240
  have eq4951337 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq320 x
       have i₂ := eq4951281
       grind)
    | exact superpose eq4951281 eq320
    | exact resolve eq320 eq4951281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq4951281
  have eq4956298 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3122573 eq3121124
    | exact resolve eq3121124 eq3122573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121124 eq3122573
  have eq4957020 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq4956298
  have eq4957092 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4957020
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4957020
    | exact resolve eq4957020 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957020
  have eq4957286 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq4957092 eq205974
    | (have j0 := eq205974 (σ (M.op x y)) (σ x) x
       grind)
    | exact resolve eq205974 eq4957092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205974 eq4957092
  have eq4957295 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4957286 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957286
  have eq5166961 : ∀ X0 : G, x ≠ (M.op (M.op x X0) x) ∨ x = (k (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq861650 x x
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq861650
    | exact resolve eq861650 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861650
  have eq5169333 : x ≠ (k x (M.op x y)) ∨ x = (k (M.op x (k x (M.op x y))) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2797960 eq5166961
    | (have j0 := eq5166961 (k x (M.op x y))
       grind)
    | (have r₁ := eq5166961 y
       have r₂ := eq2797960 x
       grind)
    | exact resolve eq5166961 eq2797960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797960 eq5166961
  have eq5169342 : x = (k (M.op x (k x (M.op x y))) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq5169333
       have r₂ := eq2744358
       grind)
    | exact resolve eq5169333 eq2744358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744358 eq5169333
  have eq5336644 : x ≠ x ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq2721961 eq457951
    | (have j0 := eq457951 (M.op x y) x
       grind)
    | (have r₁ := eq457951 (M.op x y) x
       have r₂ := eq2721961
       grind)
    | exact resolve eq457951 eq2721961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457951 eq2721961
  have eq5337028 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq5336644
  have eq5350082 : (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq5337028 eq750
    | exact resolve eq750 eq5337028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq5337028
  have eq5350451 : (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq50 eq5350082
    | exact resolve eq5350082 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq5350082
  have eq5350534 : (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (k (σ x) (σ (M.op x y)))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq20 eq5350451
    | exact resolve eq5350451 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350451
  have eq5448066 : ∀ X0 : G, (τ (σ (M.op x y))) = (M.op (M.op X0 (τ (σ (M.op x y)))) (τ (k (σ x) (σ (M.op x y))))) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5350534 eq1479
    | exact resolve eq1479 eq5350534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq5350534
  have eq5448203 : ∀ X0 : G, (τ (σ (M.op x y))) = (M.op (M.op X0 (τ (σ (M.op x y)))) (k x (M.op x y))) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq64 eq5448066
    | exact resolve eq5448066 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq5448066
  have eq5448212 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (k x (M.op x y))) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq5448203
    | exact resolve eq5448203 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5448203
  have eq5464704 : (M.op x y) = (M.op x (k x (M.op x y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq256 eq5448212
    | exact resolve eq5448212 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq5448212
  have eq5464878 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq5464704 eq5169342
    | exact resolve eq5169342 eq5464704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5169342 eq5464704
  have eq5465009 : x = (k (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | (have r₁ := eq5464878
       have r₂ := eq2767125
       grind)
    | exact resolve eq5464878 eq2767125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767125 eq5464878
  have eq5465116 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq5465009 eq2799231
    | exact resolve eq2799231 eq5465009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799231 eq5465009
  have eq5465544 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq5465116
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq5465116
    | exact resolve eq5465116 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465116
  have eq5465545 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5465544
  have eq5466035 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5465545 eq45
    | exact resolve eq45 eq5465545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5465545
  have eq5466417 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5466035
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5466035
    | exact resolve eq5466035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5466035
  have eq5466696 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq23028 eq5466417
    | exact resolve eq5466417 eq23028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23028 eq5466417
  have eq5495132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq5466696 eq4957295
    | exact resolve eq4957295 eq5466696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957295 eq5466696
  have eq5495227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq5495132
  have eq5495256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq26 eq5495227
    | exact resolve eq5495227 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495227
  have eq5495276 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq5495256
       have r₂ := eq27
       grind)
    | exact resolve eq5495256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495256
  have eq5495290 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5495276 eq2799018
    | exact resolve eq2799018 eq5495276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799018 eq5495276
  have eq5495470 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5495290
  have eq5495504 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq5495470
    | exact resolve eq5495470 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495470
  have eq5495513 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5495504
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq5495504
    | exact resolve eq5495504 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495504
  have eq5495514 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5495513
  have eq5495558 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5495514 eq2722130
    | exact resolve eq2722130 eq5495514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722130
  have eq5495728 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5495558 eq5495514
    | exact resolve eq5495514 eq5495558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5495514 eq5495558
  have eq5495889 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5495728
  have eq5495927 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5495889 eq28
    | exact resolve eq28 eq5495889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5495889
  have eq5499701 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq5495927
    | exact resolve eq5495927 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5495927
  have eq5499702 : x = (M.op x y) := by grind
  clear eq5499701
  have eq5501129 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq5499702 eq20
    | exact resolve eq20 eq5499702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq5501145 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5499702 eq147
    | exact resolve eq147 eq5499702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq5502237 : y = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5499702 eq4951337
    | exact resolve eq4951337 eq5499702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951337 eq5499702
  have eq5502557 : x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5502237
       have i₂ := eq2720060
       grind)
    | exact superpose eq2720060 eq5502237
    | exact resolve eq5502237 eq2720060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720060 eq5502237
  have eq5502558 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq5502557
  have eq5503187 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5501145
       have i₂ := eq123
       grind)
    | exact superpose eq123 eq5501145
    | exact resolve eq5501145 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq5501145
  have eq5503202 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5501129
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5501129
    | exact resolve eq5501129 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5501129
  have eq5503683 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2722940 eq5503187
    | exact resolve eq5503187 eq2722940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722940 eq5503187
  have eq5504621 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5503202 eq26
    | exact resolve eq26 eq5503202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5509421 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5503202 eq5503683
    | exact resolve eq5503683 eq5503202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5503683
  have eq5510817 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5502558 eq2724979
    | exact resolve eq2724979 eq5502558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724979 eq5502558
  have eq5511034 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq5510817
    | exact resolve eq5510817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5510817
  have eq5511166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5503202 eq5511034
    | exact resolve eq5511034 eq5503202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5511034
  have eq5511265 : x = y := by
    first
    | (have r₁ := eq5511166
       have r₂ := eq27
       grind)
    | exact resolve eq5511166 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5511166
  have eq5511617 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5511265
       grind)
    | exact superpose eq5511265 eq24
    | exact resolve eq24 eq5511265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5511265
  have eq5513712 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5511617
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5511617
    | exact resolve eq5511617 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5511617
  have eq5514404 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5503202 eq5513712
    | exact resolve eq5513712 eq5503202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5503202 eq5513712
  have eq5519066 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5514404 eq5504621
    | exact resolve eq5504621 eq5514404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504621 eq5514404
  have eq5519074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5509421 eq5519066
    | exact resolve eq5519066 eq5509421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509421 eq5519066
  have eq5519770 : False := by grind
  exact eq5519770

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq329 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
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
  have eq348 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq349 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq350 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq347 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq347 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq347 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq366 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq350 (σ X0)
       grind)
    | exact superpose eq350 eq15
    | exact resolve eq15 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq366 X0
       have i₂ := eq350 X0
       grind)
    | exact superpose eq350 eq366
    | exact resolve eq366 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq433 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq61
    | exact resolve eq61 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) X1 (σ X0)
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq67
    | exact resolve eq67 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq349 X0 (τ X1)
       grind)
    | exact superpose eq349 eq18
    | (have j1 := eq349 X0 (τ X1)
       grind)
    | exact resolve eq18 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq480 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq349 (σ X0) (σ X1)
       grind)
    | exact superpose eq349 eq15
    | (have j1 := eq349 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq1074 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq477 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq477
    | exact resolve eq477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1136 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1074 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1074
    | (have j0 := eq1074 X0 X1
       grind)
    | exact resolve eq1074 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1892 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq480 x y
       grind)
    | exact superpose eq480 eq16
    | (have j1 := eq480 x y
       grind)
    | exact resolve eq16 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1937 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq2082 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1892
       have i₂ := eq1136 y x
       grind)
    | exact superpose eq1136 eq1892
    | (have j1 := eq1136 (σ y) (σ x)
       grind)
    | (have r₁ := eq1892
       have r₂ := eq1136 y x
       grind)
    | exact resolve eq1892 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892
  have eq2083 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2082
  have eq2092 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2083
       grind)
    | exact superpose eq2083 eq61
    | exact resolve eq61 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2093 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y x
       have i₂ := eq2083
       grind)
    | exact superpose eq2083 eq62
    | exact resolve eq62 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2154 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2093 y
       have i₂ := eq2083
       grind)
    | exact superpose eq2083 eq2093
    | exact resolve eq2093 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083 eq2093
  have eq2172 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2154
  have eq2186 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq2172
       grind)
    | exact superpose eq2172 eq61
    | exact resolve eq61 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2343 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2186 (M.op x (σ x))
       have i₂ := eq2186 x
       grind)
    | exact superpose eq2186 eq2186
    | exact resolve eq2186 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186
  have eq2370 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2343
  have eq2373 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2370
       have i₂ := eq385 x
       grind)
    | exact superpose eq385 eq2370
    | exact resolve eq2370 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq2405 : ∀ X0 X1 : G, (σ x) = (σ (M.op x x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq69 x X1 x x
       have i₂ := eq2373
       grind)
    | exact superpose eq2373 eq69
    | exact resolve eq69 eq2373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2373
  have eq2634 : ∀ X0 X1 : G, (M.op x x) = (τ (σ x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2405 X0 X1
       grind)
    | exact superpose eq2405 eq10
    | (have j1 := eq2405 X0 X1
       grind)
    | exact resolve eq10 eq2405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2693 : ∀ X0 X1 : G, x = (M.op x x) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2634 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2634
    | (have j0 := eq2634 X0 X1
       grind)
    | exact resolve eq2634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634
  have eq2725 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op (M.op (M.op X1 X2) x) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 x X1 x
       have i₂ := eq2693 X0 X1
       grind)
    | exact superpose eq2693 eq67
    | (have j1 := eq2693 X1 X2
       grind)
    | exact resolve eq67 eq2693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2693
  have eq2790 : ∀ X0 X1 : G, x ≠ x ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2725 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2791 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq2790 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790
  have eq2844 : x = (M.op x x) := by
    first
    | (have i₁ := eq2791 (M.op x x) x
       have i₂ := eq2791 x x
       grind)
    | exact superpose eq2791 eq2791
    | exact resolve eq2791 eq2791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2859 : ∀ X2 : G, x = (M.op x (M.op x X2)) := by
    intro X2
    first
    | (have i₁ := eq61 (M.op (M.op x x) x) x X2
       have i₂ := eq2791 x x
       grind)
    | exact superpose eq2791 eq61
    | exact resolve eq61 eq2791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2791
  have eq2877 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq436 x x
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq436
    | exact resolve eq436 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq2927 : ∀ X0 : G, x ≠ x ∨ x = (M.op (M.op x X0) x) ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x (M.op x X0)
       have i₂ := eq2859 X0
       grind)
    | exact superpose eq2859 eq13
    | (have j0 := eq13 x (M.op x X0)
       grind)
    | (have r₁ := eq13 x (M.op x x)
       have r₂ := eq2859 x
       grind)
    | exact resolve eq13 eq2859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq2941 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ (M.op x x) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq2927 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927
  have eq2942 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2941 X0
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq2941
    | (have j0 := eq2941 X0
       grind)
    | exact resolve eq2941 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2941
  have eq3040 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (M.op X0 (σ x))
       have i₂ := eq2877 X0
       grind)
    | exact superpose eq2877 eq12
    | (have j0 := eq12 (σ x) (M.op X0 (σ x))
       grind)
    | (have r₁ := eq12 (σ x) (M.op X0 (σ x))
       have r₂ := eq2877 X0
       grind)
    | exact resolve eq12 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877
  have eq3054 : ∀ X0 : G, (k (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq3040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3596 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x X0))) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1937 x (M.op x X0)
       have i₂ := eq2942 X0
       grind)
    | exact superpose eq2942 eq1937
    | (have j0 := eq1937 x (M.op x X0)
       have j1 := eq2942 X0
       grind)
    | exact resolve eq1937 eq2942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937 eq2942
  have eq3601 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (M.op x X0))) ∨ x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have j0 := eq3596 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq3697 : ∀ X0 : G, (k x (τ (M.op X0 (σ x)))) = (τ (M.op (σ x) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq28 x (M.op X0 (σ x))
       have i₂ := eq3054 X0
       grind)
    | exact superpose eq3054 eq28
    | exact resolve eq28 eq3054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3054
  have eq3848 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k x (τ (M.op (M.op (σ x) X0) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq3697 (M.op (σ x) X0)
       have i₂ := eq62 (σ x) X0 (σ x)
       grind)
    | exact superpose eq62 eq3697
    | exact resolve eq3697 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq3697
  have eq4656 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3601 (M.op y x)
       have i₂ := eq2092 x
       grind)
    | exact superpose eq2092 eq3601
    | exact resolve eq3601 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601
  have eq4701 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4656
  have eq4717 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2092 x
       have i₂ := eq4701
       grind)
    | exact superpose eq4701 eq2092
    | exact resolve eq2092 eq4701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092 eq4701
  have eq4745 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4717
  have eq4746 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4745
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq4745
    | exact resolve eq4745 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4745
  have eq4747 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4746
       grind)
    | exact superpose eq4746 eq16
    | exact resolve eq16 eq4746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4746
  have eq4768 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4747
       have r₂ := eq385 x
       grind)
    | exact resolve eq4747 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4747
  have eq4773 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4768
       grind)
    | exact superpose eq4768 eq16
    | exact resolve eq16 eq4768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4780 : (σ y) = (M.op (σ x) (σ (M.op y y))) := by
    first
    | (have i₁ := eq433 y (σ x)
       have i₂ := eq4768
       grind)
    | exact superpose eq4768 eq433
    | exact resolve eq433 eq4768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq4784 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4768
       grind)
    | exact superpose eq4768 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4768
       grind)
    | exact resolve eq13 eq4768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4768
  have eq4801 : (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq4784
  have eq4802 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4801
       have i₂ := eq385 x
       grind)
    | exact superpose eq385 eq4801
    | exact resolve eq4801 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq4801
  have eq4810 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4802
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4802
    | exact resolve eq4802 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4802
  have eq4813 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4810
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq4810
    | exact resolve eq4810 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810
  have eq4827 : (τ (σ y)) = (k x (τ (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq3848 (σ (M.op y y))
       have i₂ := eq4780
       grind)
    | exact superpose eq4780 eq3848
    | exact resolve eq3848 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3848 eq4780
  have eq4861 : y = (k x (τ (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq4827
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4827
    | exact resolve eq4827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827
  have eq5338 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1136 y x
       have i₂ := eq4813
       grind)
    | exact superpose eq4813 eq1136
    | (have j0 := eq1136 y x
       grind)
    | exact resolve eq1136 eq4813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq4813
  have eq5391 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq5338
       have r₂ := eq4773
       grind)
    | exact resolve eq5338 eq4773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5338
  have eq5419 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4773
       have i₂ := eq5391
       grind)
    | exact superpose eq5391 eq4773
    | exact resolve eq4773 eq5391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5391
  have eq5458 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq5419
  have eq5462 : y = (k x (τ (σ x))) := by
    first
    | (have i₁ := eq4861
       have i₂ := eq5458
       grind)
    | exact superpose eq5458 eq4861
    | exact resolve eq4861 eq5458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4861 eq5458
  have eq5509 : y = (k x x) := by
    first
    | (have i₁ := eq5462
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5462
    | exact resolve eq5462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5462
  have eq5517 : y = (M.op x x) := by
    first
    | (have i₁ := eq5509
       have i₂ := eq350 x
       grind)
    | exact superpose eq350 eq5509
    | exact resolve eq5509 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq5509
  have eq5519 : x = y := by
    first
    | (have i₁ := eq5517
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq5517
    | exact resolve eq5517 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517
  have eq5543 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4773
       have i₂ := eq5519
       grind)
    | exact superpose eq5519 eq4773
    | exact resolve eq4773 eq5519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4773 eq5519
  have eq5564 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5543
       have i₂ := eq2844
       grind)
    | exact superpose eq2844 eq5543
    | exact resolve eq5543 eq2844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844 eq5543
  have eq5565 : False := by grind
  exact eq5565

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pxx_y_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq20 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq19 X2 X0 x
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = (M.op (M.op X0 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X2) (M.op X1 X0)
       have i₂ := eq19 X1 X0 X2
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 (M.op X0 X2) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (σ X1) (σ X0)
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X0
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X1) (σ X0) X2
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X0
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq187 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq187 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq202 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq224 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 X2 X3 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq38
    | exact resolve eq38 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq959 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq197 (τ X1) (τ X0)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq197
    | (have j0 := eq197 (τ X1) (τ X0)
       grind)
    | exact resolve eq197 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq959 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq959
    | (have j0 := eq959 X0 X1
       grind)
    | exact resolve eq959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq988 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq979 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq979
    | (have j0 := eq979 X0 X1
       grind)
    | exact resolve eq979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq996 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq988 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq988
    | (have j0 := eq988 X0 X1
       grind)
    | exact resolve eq988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1003 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq996 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq996
    | (have j0 := eq996 X0 X1
       grind)
    | exact resolve eq996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1008 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1003 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1003
    | (have j0 := eq1003 X0 X1
       grind)
    | exact resolve eq1003 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1011 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1008 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1008
    | (have j0 := eq1008 X0 X1
       grind)
    | exact resolve eq1008 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1293 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq202 (τ X1) (τ X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq202
    | (have j0 := eq202 (τ X0) (τ X1)
       grind)
    | exact resolve eq202 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1317 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1293 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1293
    | (have j0 := eq1293 X0 X1
       grind)
    | exact resolve eq1293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1327 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1317 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1317
    | (have j0 := eq1317 X0 X1
       grind)
    | exact resolve eq1317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1335 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1327 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1327
    | (have j0 := eq1327 X0 X1
       grind)
    | exact resolve eq1327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1342 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1335 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1335
    | (have j0 := eq1335 X0 X1
       grind)
    | exact resolve eq1335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1345 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1342 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1342
    | (have j0 := eq1342 X0 X1
       grind)
    | exact resolve eq1342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1348 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1345 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1345
    | (have j0 := eq1345 X0 X1
       grind)
    | exact resolve eq1345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq1724 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X1 X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq189 X0 X1 X2
       grind)
    | exact superpose eq189 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq189 X1 X0 X2
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq189 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq189 X0 X0 X2
       grind)
    | exact resolve eq13 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1738 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X1 X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq189 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1741 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X1 X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1724 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq1742 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X1 X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1741 X0 X1 X2
       have j1 := eq1738 X0 X1 X2
       grind)
    | (have r₁ := eq1741 X0 X1 X2
       have r₂ := eq1738 X0 X1 X2
       grind)
    | (have r₁ := eq1741 X1 X0 X2
       have r₂ := eq1738 X0 X1 X2
       grind)
    | exact resolve eq1741 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738 eq1741
  have eq1746 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X1 X0))) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1742 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1742
    | (have j0 := eq1742 X0 X1 X2
       grind)
    | exact resolve eq1742 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742
  have eq1935 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ (k X1 X0)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq190 X0 X1 X2
       grind)
    | exact superpose eq190 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq190 X1 X0 X2
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq190 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq190 X0 X0 X2
       grind)
    | exact resolve eq13 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1949 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X1) ∨ (σ X1) = (M.op (σ (k X1 X0)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq190 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1952 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ (k X1 X0)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1935 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935
  have eq1953 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ (k X1 X0)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1952 X0 X1 X2
       have j1 := eq1949 X0 X1 X2
       grind)
    | (have r₁ := eq1952 X0 X1 X2
       have r₂ := eq1949 X0 X1 X2
       grind)
    | (have r₁ := eq1952 X1 X0 X2
       have r₂ := eq1949 X0 X1 X2
       grind)
    | exact resolve eq1952 eq1949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949 eq1952
  have eq1957 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ (k X1 X0)) (M.op (σ X1) X2)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1953 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1953
    | (have j0 := eq1953 X0 X1 X2
       grind)
    | exact resolve eq1953 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq3442 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3468 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) X2)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (σ X0) X2
       have i₂ := eq78 X1 X0
       grind)
    | exact superpose eq78 eq19
    | (have j1 := eq78 X1 X0
       grind)
    | exact resolve eq19 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3497 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3442 X0 X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq3442
    | (have j0 := eq3442 X0 X1
       grind)
    | exact resolve eq3442 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442
  have eq3507 : ∀ X0 X1 X2 : G, (τ X0) = (τ (k (M.op X0 X2) (M.op X1 X0))) ∨ (M.op X0 X2) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3497 (M.op x x) (M.op X0 x)
       have i₂ := eq19 X0 x x
       grind)
    | exact superpose eq19 eq3497
    | (have j0 := eq3497 X2 X0
       grind)
    | exact resolve eq3497 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3513 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq3497 X0 X1
       grind)
    | exact superpose eq3497 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq3497 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq3497 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq3497 X0 X0
       grind)
    | exact resolve eq13 eq3497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3514 : ∀ X0 X1 X2 : G, (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X2) = X2 ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X0 X2
       have i₂ := eq3497 X2 X0
       grind)
    | exact superpose eq3497 eq19
    | (have j1 := eq3497 X2 X0
       grind)
    | exact resolve eq19 eq3497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3541 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3497 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3545 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3513 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513
  have eq3553 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3545 X0 X1
       have j1 := eq3541 X0 X1
       grind)
    | (have r₁ := eq3545 X1 X1
       have r₂ := eq3541 (k X1 X1) X1
       grind)
    | (have r₁ := eq3545 X0 X1
       have r₂ := eq3541 X0 (k X1 X0)
       grind)
    | (have r₁ := eq3545 X0 X1
       have r₂ := eq3541 X0 X1
       grind)
    | exact resolve eq3545 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545
  have eq3566 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3541 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3541
  have eq3621 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3566 (M.op x x)
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq3566
    | (have j0 := eq3566 X0
       grind)
    | exact resolve eq3566 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3625 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq3566 X0
       grind)
    | exact superpose eq3566 eq12
    | (have j1 := eq3566 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3566 X0
       grind)
    | exact resolve eq12 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq3653 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3625 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625
  have eq3673 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3653 X0
       grind)
    | exact superpose eq3653 eq11
    | (have j1 := eq3653 X0
       grind)
    | exact resolve eq11 eq3653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3653
  have eq3780 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3673 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3673
    | (have j0 := eq3673 X0
       grind)
    | exact resolve eq3673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673
  have eq3889 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3780 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4133 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq3621 X0
       grind)
    | exact superpose eq3621 eq12
    | (have j1 := eq3621 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3621 X0
       grind)
    | exact resolve eq12 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621
  have eq4162 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4133 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133
  have eq4589 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4162 (σ x)
       have i₂ := eq77 x x
       grind)
    | exact superpose eq77 eq4162
    | (have j0 := eq4162 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | exact resolve eq4162 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq4162
  have eq4651 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4589 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589
  have eq4706 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4651 X0
       have j1 := eq3889 (σ X0)
       grind)
    | (have r₁ := eq4651 X0
       have r₂ := eq3889 (σ X0)
       grind)
    | exact resolve eq4651 eq3889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889 eq4651
  have eq4713 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (k X0 X0))) (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4706 X0
       have i₂ := eq32 (σ (k X0 X0)) (k X0 X0)
       grind)
    | exact superpose eq32 eq4706
    | (have j0 := eq4706 X0
       grind)
    | exact resolve eq4706 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4706
  have eq4719 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4713 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq4713
    | (have j0 := eq4713 X0
       grind)
    | exact resolve eq4713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4713
  have eq4725 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4719 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4719
    | (have j0 := eq4719 X0
       grind)
    | exact resolve eq4719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4731 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4725 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4725
    | (have j0 := eq4725 X0
       grind)
    | exact resolve eq4725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4725
  have eq4883 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq224 (τ X0) X0 (τ X0) X0
       have i₂ := eq4731 (τ X0)
       grind)
    | exact superpose eq4731 eq224
    | (have j1 := eq4731 (τ X0)
       grind)
    | exact resolve eq224 eq4731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq4731
  have eq4910 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4883 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4883
    | (have j0 := eq4883 X0
       grind)
    | exact resolve eq4883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4883
  have eq4920 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4910 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4910
    | (have j0 := eq4910 X0
       grind)
    | exact resolve eq4910 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4910
  have eq4929 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4920 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4920
    | (have j0 := eq4920 X0
       grind)
    | exact resolve eq4920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4920
  have eq4936 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4929 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq4929
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq4929 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4951 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3780 (k X0 X0)
       have i₂ := eq4929 X0
       grind)
    | exact superpose eq4929 eq3780
    | (have j0 := eq3780 X0
       have j1 := eq4929 X0
       grind)
    | exact resolve eq3780 eq4929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3780
  have eq4968 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4951 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951
  have eq4970 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4936 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4936
  have eq5054 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 (k X0 X0) X1 (k X0 X0)
       have i₂ := eq4968 X0
       grind)
    | exact superpose eq4968 eq25
    | (have j1 := eq4968 X0
       grind)
    | exact resolve eq25 eq4968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4968
  have eq5081 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4929 (M.op X0 X0)
       have i₂ := eq4970 X0
       grind)
    | exact superpose eq4970 eq4929
    | (have j1 := eq4970 X0
       grind)
    | exact resolve eq4929 eq4970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4929 eq4970
  have eq5101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5081
  have eq5105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5101 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq5101 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq5101 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101
  have eq5236 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5105 (σ X0)
       grind)
    | exact superpose eq5105 eq15
    | exact resolve eq15 eq5105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5248 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq5105 (τ X0)
       grind)
    | exact superpose eq5105 eq43
    | exact resolve eq43 eq5105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5310 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5248 X0
       have i₂ := eq5105 X0
       grind)
    | exact superpose eq5105 eq5248
    | exact resolve eq5248 eq5105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5248
  have eq5318 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5236 X0
       have i₂ := eq5105 X0
       grind)
    | exact superpose eq5105 eq5236
    | exact resolve eq5236 eq5105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5236
  have eq5517 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (τ X0) (τ X0) x
       have i₂ := eq5310 X0
       grind)
    | exact superpose eq5310 eq20
    | exact resolve eq20 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5523 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (τ X0) X1 (τ X0)
       have i₂ := eq5310 X0
       grind)
    | exact superpose eq5310 eq34
    | exact resolve eq34 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq5541 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) ∨ (τ X0) ≠ (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5523 X0 X1
       have i₂ := eq5310 (M.op X0 X0)
       grind)
    | exact superpose eq5310 eq5523
    | (have j0 := eq5523 X0 X1
       grind)
    | exact resolve eq5523 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5523
  have eq5557 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5541 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq5541 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq5541
    | (have j0 := eq5541 X0 X1
       grind)
    | exact resolve eq5541 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5541
  have eq5714 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) X1 (σ X0)
       have i₂ := eq5318 X0
       grind)
    | exact superpose eq5318 eq25
    | exact resolve eq25 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6544 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq1746 X1 X0 X2
       grind)
    | exact superpose eq1746 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq1746 X1 X0 X2
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq1746 X0 X1 X2
       grind)
    | exact resolve eq12 eq1746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq6566 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6544 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6544
  have eq6575 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6566 X0 X1 X2
       have i₂ := eq5318 X0
       grind)
    | exact superpose eq5318 eq6566
    | (have j0 := eq6566 X0 X1 X2
       grind)
    | exact resolve eq6566 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6566
  have eq6581 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6575 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6575
    | (have j0 := eq6575 X0 X1 X2
       grind)
    | exact resolve eq6575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6575
  have eq7483 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq1957 X1 X0 X2
       grind)
    | exact superpose eq1957 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq1957 X1 X0 X2
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq1957 X0 X1 X2
       grind)
    | exact resolve eq12 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq7506 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq7483 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7483
  have eq7516 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7506 X0 X1 X2
       have i₂ := eq5318 X0
       grind)
    | exact superpose eq5318 eq7506
    | (have j0 := eq7506 X0 X1 X2
       grind)
    | exact resolve eq7506 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7506
  have eq7523 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7516 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7516
    | (have j0 := eq7516 X0 X1 X2
       grind)
    | exact resolve eq7516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7516
  have eq19729 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3553 X0 X1
       grind)
    | exact superpose eq3553 eq11
    | (have j1 := eq3553 X0 X1
       grind)
    | exact resolve eq11 eq3553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq19859 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19729 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq19729
    | (have j0 := eq19729 X0 X1
       grind)
    | exact resolve eq19729 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19729
  have eq20142 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq19859 (τ X0) X1
       grind)
    | exact superpose eq19859 eq18
    | (have j1 := eq19859 (τ X0) X1
       grind)
    | exact resolve eq18 eq19859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19859
  have eq23419 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (M.op X0 X0))) ∨ (τ (σ X0)) = (k (τ (σ (M.op X0 X0))) (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5557 (σ X0) X1
       have i₂ := eq5318 X0
       grind)
    | exact superpose eq5318 eq5557
    | exact resolve eq5557 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23456 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (M.op X0 X0) ∨ (τ (σ X0)) = (k (τ (σ (M.op X0 X0))) (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23419 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq23419
    | (have j0 := eq23419 X0 X1
       grind)
    | exact resolve eq23419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23419
  have eq23473 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (τ (σ X0)) = (k (τ (σ (M.op X0 X0))) (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23456 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23456
    | (have j0 := eq23456 X0 X1
       grind)
    | exact resolve eq23456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23456
  have eq23484 : ∀ X0 X1 : G, (k (τ (σ (M.op X0 X0))) (M.op X1 X0)) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23473 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23473
    | (have j0 := eq23473 X0 X1
       grind)
    | exact resolve eq23473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23473
  have eq23494 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23484 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq23484
    | (have j0 := eq23484 X0 X1
       grind)
    | exact resolve eq23484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23484
  have eq37030 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (M.op X0 X1) (M.op X2 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (M.op X0 X1) (M.op X2 X0))
       have i₂ := eq3507 X0 X2 X1
       grind)
    | exact superpose eq3507 eq11
    | (have j1 := eq3507 X0 X2 X1
       grind)
    | exact resolve eq11 eq3507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507
  have eq37205 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37030 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37030
    | (have j0 := eq37030 X0 X1 X2
       grind)
    | exact resolve eq37030 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37030
  have eq38107 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37205 (τ X0) (τ X0) x
       have i₂ := eq5310 X0
       grind)
    | exact superpose eq5310 eq37205
    | (have j0 := eq37205 (τ X0) X1 X1
       grind)
    | exact resolve eq37205 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37205
  have eq38375 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq38107 X0 X1
       have j1 := eq5557 X0 X1
       grind)
    | (have r₁ := eq38107 X0 X1
       have r₂ := eq5557 X0 X1
       grind)
    | exact resolve eq38107 eq5557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5557 eq38107
  have eq38476 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38375 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38375
    | exact resolve eq38375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38375
  have eq38634 : ∀ X0 X1 : G, (k (τ (σ (M.op X0 X0))) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38476 X0 X1
       have i₂ := eq5318 X0
       grind)
    | exact superpose eq5318 eq38476
    | (have j0 := eq38476 X0 X1
       grind)
    | exact resolve eq38476 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38476
  have eq38711 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38634 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq38634
    | (have j0 := eq38634 X0 X1
       grind)
    | exact resolve eq38634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38634
  have eq59363 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (M.op (M.op X2 X0) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq3514 X0 X2 X1
       grind)
    | exact superpose eq3514 eq11
    | (have j1 := eq3514 X0 X2 X1
       grind)
    | exact resolve eq11 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514
  have eq59520 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59363 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq59363
    | (have j0 := eq59363 X0 X1 X2
       grind)
    | exact resolve eq59363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59363
  have eq124596 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq20142 X0 X1
       grind)
    | exact superpose eq20142 eq18
    | (have j1 := eq20142 X0 X1
       grind)
    | exact resolve eq18 eq20142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20142
  have eq124941 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124596 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq124596
    | (have j0 := eq124596 X0 X1
       grind)
    | exact resolve eq124596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124596
  have eq126215 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op (τ (σ X1)) X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq124941 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq124941
    | (have j0 := eq124941 (σ X1) X0
       grind)
    | exact resolve eq124941 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124941
  have eq126573 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq126215 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq126215
    | (have j0 := eq126215 X0 X1
       grind)
    | exact resolve eq126215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126215
  have eq126665 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq126573 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq126573
    | (have j0 := eq126573 X0 X1
       grind)
    | exact resolve eq126573 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126573
  have eq127023 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq184
       have i₂ := eq126665 y x
       grind)
    | exact superpose eq126665 eq184
    | (have j1 := eq126665 y x
       grind)
    | (have r₁ := eq184
       have r₂ := eq126665 y x
       grind)
    | exact resolve eq184 eq126665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq126665
  have eq127246 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq127023
  have eq127295 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq197 x y
       grind)
    | (have r₁ := eq127246
       have r₂ := eq197 x y
       grind)
    | exact resolve eq127246 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq127246
  have eq128835 : y ≠ y ∨ (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq127295
       grind)
    | exact superpose eq127295 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq127295
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq127295
       grind)
    | exact resolve eq12 eq127295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128877 : (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq128835
  have eq245802 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X2 X0) = X2 ∨ (k (τ X0) (τ X2)) = (τ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3468 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3468
    | exact resolve eq3468 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq246169 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (τ (k X0 X2)) = (τ (M.op X2 X0)) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq245802 X0 X1 X2
       have i₂ := eq43 X2 X0
       grind)
    | exact superpose eq43 eq245802
    | (have j0 := eq245802 X0 X1 X2
       grind)
    | exact resolve eq245802 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245802
  have eq246438 : ∀ X0 X1 X3 : G, (τ (k X0 X3)) = (τ (M.op X3 X0)) ∨ (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X3 X0) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq19 X1 X0 (M.op X0 x)
       have i₂ := eq246169 X0 x X3
       grind)
    | exact superpose eq246169 eq19
    | (have j1 := eq246169 X0 X1 X3
       grind)
    | exact resolve eq19 eq246169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246169
  have eq247138 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op (M.op X2 X1) X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq246438 X1 X2 X0
       grind)
    | exact superpose eq246438 eq11
    | (have j1 := eq246438 X1 X2 X0
       grind)
    | exact resolve eq11 eq246438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246438
  have eq247355 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq247138 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq247138
    | (have j0 := eq247138 X0 X1 X2
       grind)
    | exact resolve eq247138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247138
  have eq247873 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op X0 (M.op X0 X2)) ∨ (M.op X3 (M.op X0 X2)) = (k (M.op X0 X2) X3) ∨ (M.op X3 (M.op X0 X2)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq247355 X3 (M.op X0 X2) (M.op x X0)
       have i₂ := eq19 x X0 X2
       grind)
    | exact superpose eq19 eq247355
    | (have j0 := eq247355 X3 (M.op X0 X2) X2
       grind)
    | exact resolve eq247355 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247355
  have eq316247 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X1))) (σ (τ (k X0 X1)))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6581 (τ X1) (τ X0) X2
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq6581
    | exact resolve eq6581 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6581
  have eq316742 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op X2 (σ (τ X1))) (k X0 X1)) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq316247 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq316247
    | (have j0 := eq316247 X0 X1 X2
       grind)
    | exact resolve eq316247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316247
  have eq316894 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq316742 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq316742
    | (have j0 := eq316742 X0 X1 X2
       grind)
    | exact resolve eq316742 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316742
  have eq316974 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (σ (τ (M.op X0 X0))) ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq316894 X0 X1 X2
       have i₂ := eq5310 X0
       grind)
    | exact superpose eq5310 eq316894
    | (have j0 := eq316894 X0 X1 X2
       grind)
    | exact resolve eq316894 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316894
  have eq317044 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq316974 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq316974
    | (have j0 := eq316974 X0 X1 X2
       grind)
    | exact resolve eq316974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316974
  have eq317089 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq317044 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq317044
    | (have j0 := eq317044 X0 X1 X2
       grind)
    | exact resolve eq317044 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317044
  have eq317116 : ∀ X0 X1 X2 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (M.op X2 X1) (k X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq317089 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq317089
    | (have j0 := eq317089 X0 X1 X2
       grind)
    | exact resolve eq317089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317089
  have eq317130 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq317116 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq317116
    | (have j0 := eq317116 X0 X1 X2
       grind)
    | exact resolve eq317116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317116
  have eq317630 : ∀ X0 X2 X3 : G, (k X2 X0) = (M.op X0 (M.op (k X2 X0) X3)) ∨ (M.op X2 X2) = (k X2 X0) ∨ (k X2 X0) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq19 (M.op x X0) (k X2 X0) X3
       have i₂ := eq317130 X2 X0 x
       grind)
    | exact superpose eq317130 eq19
    | (have j1 := eq317130 X2 X0 X2
       grind)
    | exact resolve eq19 eq317130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317130
  have eq318785 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f318785_16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
      intro X0 X1 X2 X3
      grind
    have f318785_18 : ∀ X0 : G, (σ (τ X0)) = X0 := by
      intro X0
      grind
    have f318785_19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
      intro X0 X1
      grind
    have f318785_20 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
      intro X0 X1
      grind
    have f318785_21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
      intro X0 X1
      grind
    have f318785_24 : (σ (τ X0)) ≠ (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) := by grind
    have f318785_26 : (σ (τ (k X0 X1))) ≠ (σ (τ X1)) := by grind
    have f318785_27 : (k X0 X1) ≠ (σ (τ X1)) := by
      first
      | (have i₁ := f318785_26
         have i₂ := f318785_18 (k X0 X1)
         grind)
      | exact superpose f318785_18 f318785_26
      | exact resolve f318785_26 f318785_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_28 : X1 ≠ (k X0 X1) := by
      first
      | (have i₁ := f318785_27
         have i₂ := f318785_18 X1
         grind)
      | exact superpose f318785_18 f318785_27
      | exact resolve f318785_27 f318785_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_33 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
      intro X0 X4 X5
      first
      | (have i₁ := f318785_16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
         have i₂ := f318785_16 X0 x x x
         grind)
      | exact superpose f318785_16 f318785_16
      | exact resolve f318785_16 f318785_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_74 : X0 ≠ (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) := by
      first
      | (have i₁ := f318785_24
         have i₂ := f318785_18 X0
         grind)
      | exact superpose f318785_18 f318785_24
      | exact resolve f318785_24 f318785_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_75 : X0 ≠ (M.op (k X0 X1) (M.op X0 X2)) := by
      first
      | (have i₁ := f318785_74
         have i₂ := f318785_18 (k X0 X1)
         grind)
      | exact superpose f318785_18 f318785_74
      | exact resolve f318785_74 f318785_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_84 : X0 ≠ (M.op (M.op X1 X0) (M.op X0 X2)) ∨ X1 = (M.op X1 X0) ∨ X0 = (M.op X1 X0) := by
      first
      | (have i₁ := f318785_75
         have i₂ := f318785_21 X0 X1
         grind)
      | exact superpose f318785_21 f318785_75
      | (have j1 := f318785_21 X0 X1
         grind)
      | exact resolve f318785_75 f318785_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_90 : X1 = (M.op X1 X0) ∨ X0 = (M.op X1 X0) := by
      first
      | (have r₁ := f318785_84
         have r₂ := f318785_33 X1 X0 X2
         grind)
      | exact resolve f318785_84 f318785_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_133 : X1 ≠ X1 ∨ X1 = (k X0 X1) ∨ X0 = X1 ∨ X0 = (M.op X1 X0) := by
      first
      | (have i₁ := f318785_20 X0 X1
         have i₂ := f318785_90
         grind)
      | exact superpose f318785_90 f318785_20
      | (have j0 := f318785_20 X0 X1
         grind)
      | (have r₁ := f318785_20 X0 X1
         have r₂ := f318785_90
         grind)
      | exact resolve f318785_20 f318785_90
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_139 : X0 ≠ X1 ∨ X0 = (M.op X1 X0) := by grind
    have f318785_140 : X1 = (k X0 X1) ∨ X0 = X1 ∨ X0 = (M.op X1 X0) := by grind
    have f318785_141 : X0 = X1 ∨ X0 = (M.op X1 X0) := by
      first
      | (have r₁ := f318785_140
         have r₂ := f318785_28
         grind)
      | exact resolve f318785_140 f318785_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_142 : X0 = (M.op X1 X0) := by
      first
      | (have r₁ := f318785_141
         have r₂ := f318785_139
         grind)
      | exact resolve f318785_141 f318785_139
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_160 : X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
      first
      | (have i₁ := f318785_19 X0 X1
         have i₂ := f318785_142
         grind)
      | exact superpose f318785_142 f318785_19
      | (have j0 := f318785_19 X0 X1
         grind)
      | (have r₁ := f318785_19 X0 X1
         have r₂ := f318785_142
         grind)
      | exact resolve f318785_19 f318785_142
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_164 : (k X0 X1) = (M.op X0 X0) := by grind
    have f318785_423 : X0 ≠ (M.op (M.op X0 X0) (M.op X0 X2)) := by
      first
      | (have i₁ := f318785_75
         have i₂ := f318785_164
         grind)
      | exact superpose f318785_164 f318785_75
      | exact resolve f318785_75 f318785_164
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f318785_434 : False := by
      first
      | (have r₁ := f318785_423
         have r₂ := f318785_33 X0 X0 X2
         grind)
      | exact resolve f318785_423 f318785_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f318785_434
  clear eq7523
  have eq319446 : ∀ X0 X1 X2 : G, (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) = X0 ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq318785 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq318785
    | (have j0 := eq318785 X0 X1 X2
       grind)
    | exact resolve eq318785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318785
  have eq319570 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319446 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq319446
    | (have j0 := eq319446 X0 X1 X2
       grind)
    | exact resolve eq319446 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319446
  have eq319636 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (σ (τ (M.op X0 X0))) ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319570 X0 X1 X2
       have i₂ := eq5310 X0
       grind)
    | exact superpose eq5310 eq319570
    | (have j0 := eq319570 X0 X1 X2
       grind)
    | exact resolve eq319570 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319570
  have eq319693 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319636 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq319636
    | (have j0 := eq319636 X0 X1 X2
       grind)
    | exact resolve eq319636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319636
  have eq319731 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319693 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq319693
    | (have j0 := eq319693 X0 X1 X2
       grind)
    | exact resolve eq319693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319693
  have eq319760 : ∀ X0 X1 X2 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (k X0 X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319731 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq319731
    | (have j0 := eq319731 X0 X1 X2
       grind)
    | exact resolve eq319731 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319731
  have eq319777 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq319760 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq319760
    | (have j0 := eq319760 X0 X1 X2
       grind)
    | exact resolve eq319760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319760
  have eq340379 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq317630 X1 X0 (M.op X0 x)
       have i₂ := eq319777 X0 X1 x
       grind)
    | exact superpose eq319777 eq317630
    | (have j0 := eq317630 X1 X0 x
       have j1 := eq319777 X0 X1 x
       grind)
    | exact resolve eq317630 eq319777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317630 eq319777
  have eq340757 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq340379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340379
  have eq343296 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq340757 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340757
  have eq344116 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op (k X0 X0) (k X0 X0)) = (k (k X0 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (k (k X0 X0) (M.op X1 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq343296 (k X0 X0) (M.op X1 X0)
       have i₂ := eq5054 X0 X1
       grind)
    | exact superpose eq5054 eq343296
    | (have j0 := eq343296 (k X0 X0) (M.op X1 X0)
       have j1 := eq5054 X0 X1
       grind)
    | exact resolve eq343296 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5054 eq343296
  have eq344217 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X1 X0)) ∨ (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k (k X0 X0) (M.op X1 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq344116 X0 X1
       have i₂ := eq5105 X0
       grind)
    | exact superpose eq5105 eq344116
    | (have j0 := eq344116 X0 X1
       grind)
    | exact resolve eq344116 eq5105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344116
  have eq344352 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k (k X0 X0) (M.op X1 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq344217 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq344217 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq344217
    | (have j0 := eq344217 X0 X1
       grind)
    | exact resolve eq344217 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344217
  have eq344457 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = (k (k X0 X0) (M.op X1 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq344352 X0 X1
       have j1 := eq38711 X0 X1
       grind)
    | (have r₁ := eq344352 X0 X1
       have r₂ := eq38711 X0 X1
       grind)
    | exact resolve eq344352 eq38711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344352
  have eq344516 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X0 X0) (M.op X1 X0)) ∨ (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq344457 X0 X1
       have i₂ := eq5105 X0
       grind)
    | exact superpose eq5105 eq344457
    | (have j0 := eq344457 X0 X1
       grind)
    | exact resolve eq344457 eq5105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344457
  have eq344557 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k (M.op X0 X0) (M.op X1 X0)) ∨ (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq344516 X0 X1
       have i₂ := eq5105 X0
       grind)
    | exact superpose eq5105 eq344516
    | (have j0 := eq344516 X0 X1
       grind)
    | exact resolve eq344516 eq5105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5105 eq344516
  have eq344571 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X0 X0) (M.op X1 X0)) ∨ (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq344557 X0 X1
       have j1 := eq23494 X0 X1
       grind)
    | (have r₁ := eq344557 X0 X1
       have r₂ := eq23494 X0 X1
       grind)
    | exact resolve eq344557 eq23494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23494 eq344557
  have eq346807 : ∀ X0 X2 : G, (k (M.op X0 X0) X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq344571 X0 (M.op X2 X0)
       have i₂ := eq59520 X0 x X2
       grind)
    | exact superpose eq59520 eq344571
    | (have j1 := eq59520 X0 X2 X2
       grind)
    | exact resolve eq344571 eq59520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59520
  have eq347072 : y = (k (M.op y y) y) ∨ y = (k (M.op y y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq344571 y x
       have i₂ := eq127295
       grind)
    | exact superpose eq127295 eq344571
    | exact resolve eq344571 eq127295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127295
  have eq347247 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq344571 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344571
  have eq347268 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k (M.op y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq347072
  have eq347336 : ∀ X0 X2 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq346807 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346807
  have eq347345 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq347247 X0 X1
       have j1 := eq38711 X0 X1
       grind)
    | (have r₁ := eq347247 X0 X1
       have r₂ := eq38711 X0 X1
       grind)
    | exact resolve eq347247 eq38711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38711 eq347247
  have eq349553 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq347345 (σ X0) X1
       have i₂ := eq5318 X0
       grind)
    | exact superpose eq5318 eq347345
    | exact resolve eq347345 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349558 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq347345 (τ X0) X1
       have i₂ := eq5310 X0
       grind)
    | exact superpose eq5310 eq347345
    | exact resolve eq347345 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349639 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq347345 (M.op X0 X1) (M.op x X0)
       have i₂ := eq19 x X0 X1
       grind)
    | exact superpose eq19 eq347345
    | exact resolve eq347345 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353219 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (M.op X0 X0) (M.op X1 (σ X0))
       have i₂ := eq349553 X0 X1
       grind)
    | exact superpose eq349553 eq40
    | exact resolve eq40 eq349553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq349553
  have eq353487 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq353219 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq353219
    | exact resolve eq353219 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353219
  have eq359556 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (M.op (σ X0) X1) (M.op (σ X0) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (M.op (M.op (σ X0) X1) (M.op (σ X0) X1)) X0
       have i₂ := eq349639 (σ X0) X1
       grind)
    | exact superpose eq349639 eq32
    | exact resolve eq32 eq349639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349639
  have eq429726 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq347336 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347336
  have eq429746 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq429726 X0
       have j1 := eq247873 X0 X0 X0
       grind)
    | (have r₁ := eq429726 x
       have r₂ := eq247873 x x x
       grind)
    | exact resolve eq429726 eq247873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247873 eq429726
  have eq467362 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq429746 (M.op x x)
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq429746
    | exact resolve eq429746 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467469 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq429746 X0
       grind)
    | exact superpose eq429746 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       have j1 := eq429746 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq429746 X0
       grind)
    | exact resolve eq12 eq429746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429746
  have eq467670 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq467469 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467469
  have eq467743 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq467670 X0
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq467670 X0
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq467670
    | (have j0 := eq467670 X0
       grind)
    | exact resolve eq467670 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467670
  have eq470488 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1 (M.op X0 X0)
       have i₂ := eq467362 X0
       grind)
    | exact superpose eq467362 eq25
    | (have j1 := eq467362 X0
       grind)
    | exact resolve eq25 eq467362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470642 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (M.op (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq349558 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq467362 (τ X0)
       grind)
    | exact superpose eq467362 eq349558
    | (have j1 := eq467362 (τ X0)
       grind)
    | exact resolve eq349558 eq467362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349558 eq467362
  have eq470784 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) X0)) ∨ (M.op (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq470642 X0
       have i₂ := eq43 X0 (M.op X0 X0)
       grind)
    | exact superpose eq43 eq470642
    | (have j0 := eq470642 X0
       grind)
    | exact resolve eq470642 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470642
  have eq470901 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq470784 X0
       have i₂ := eq5310 X0
       grind)
    | exact superpose eq5310 eq470784
    | (have j0 := eq470784 X0
       grind)
    | exact resolve eq470784 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470784
  have eq471001 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k X0 (M.op X0 X0))) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq470901 X0
       have i₂ := eq43 (M.op X0 X0) X0
       grind)
    | exact superpose eq43 eq470901
    | (have j0 := eq470901 X0
       grind)
    | exact resolve eq470901 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470901
  have eq471465 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1348 (M.op X0 X0) X0
       have i₂ := eq467743 X0
       grind)
    | exact superpose eq467743 eq1348
    | (have j0 := eq1348 (M.op X0 X0) X0
       have j1 := eq467743 X0
       grind)
    | exact resolve eq1348 eq467743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq471687 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq467743 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467743
  have eq471838 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq471465 X0
       have j1 := eq471687 X0
       grind)
    | (have r₁ := eq471465 X0
       have r₂ := eq471687 X0
       grind)
    | exact resolve eq471465 eq471687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471465
  have eq472008 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq471838 X0
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq471838 X0
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq471838
    | (have j0 := eq471838 X0
       grind)
    | exact resolve eq471838 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471838
  have eq472162 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq472008 X0
       have j1 := eq471687 X0
       grind)
    | (have r₁ := eq472008 X0
       have r₂ := eq471687 X0
       grind)
    | exact resolve eq472008 eq471687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472008
  have eq474946 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq471687 (M.op x x)
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq471687
    | exact resolve eq471687 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471687
  have eq475262 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq472162 (τ X0)
       have i₂ := eq5310 X0
       grind)
    | exact superpose eq5310 eq472162
    | exact resolve eq472162 eq5310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5310 eq472162
  have eq475377 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (M.op (τ X0) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq475262 X0
       have i₂ := eq43 X0 (M.op X0 X0)
       grind)
    | exact superpose eq43 eq475262
    | (have j0 := eq475262 X0
       grind)
    | exact resolve eq475262 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475262
  have eq1432016 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq198 x y
       have i₂ := eq128877
       grind)
    | exact superpose eq128877 eq198
    | (have j0 := eq198 x y
       grind)
    | exact resolve eq198 eq128877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq128877
  have eq1432137 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1432016
  have eq1475726 : y = (k (M.op y y) (τ (σ y))) ∨ y = (k (M.op y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq353487 y (σ x)
       have i₂ := eq347268
       grind)
    | exact superpose eq347268 eq353487
    | exact resolve eq353487 eq347268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347268 eq353487
  have eq1475898 : y = (k (M.op y y) y) ∨ y = (k (M.op y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1475726
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1475726
    | exact resolve eq1475726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475726
  have eq1475899 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op y y) y) := by grind
  clear eq1475898
  have eq1477409 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k (M.op y y) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1475899
       grind)
    | exact superpose eq1475899 eq16
    | exact resolve eq16 eq1475899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1477509 : ∀ X0 : G, y = (k (M.op y y) y) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ x) (σ y) X0
       have i₂ := eq1475899
       grind)
    | exact superpose eq1475899 eq19
    | exact resolve eq19 eq1475899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1477510 : ∀ X0 : G, y = (k (M.op y y) y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ x) (σ y) x
       have i₂ := eq1475899
       grind)
    | exact superpose eq1475899 eq20
    | exact resolve eq20 eq1475899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475899
  have eq1477870 : (σ x) ≠ (σ x) ∨ y = (k (M.op y y) y) ∨ y = (M.op x y) ∨ (τ (k y x)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq1477409
       have i₂ := eq3497 y x
       grind)
    | exact superpose eq3497 eq1477409
    | (have j1 := eq3497 y x
       grind)
    | exact resolve eq1477409 eq3497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477409
  have eq1477871 : y = (M.op x y) ∨ y = (k (M.op y y) y) ∨ (τ (k y x)) = (τ (M.op x y)) := by grind
  clear eq1477870
  have eq1505069 : y = (k (M.op y y) y) ∨ y = (k (M.op y y) y) ∨ (τ (k y x)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq347345 y x
       have i₂ := eq1477871
       grind)
    | exact superpose eq1477871 eq347345
    | exact resolve eq347345 eq1477871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347345 eq1477871
  have eq1505089 : y = (k (M.op y y) y) ∨ (τ (k y x)) = (τ (M.op x y)) := by grind
  clear eq1505069
  have eq1633498 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (k X0 (M.op X0 X0)))) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5517 X0 (τ X0)
       have i₂ := eq471001 X0
       grind)
    | exact superpose eq471001 eq5517
    | (have j1 := eq471001 X0
       grind)
    | exact resolve eq5517 eq471001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517 eq471001
  have eq1735129 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (σ X0)) (τ (k (σ X0) (σ (M.op X0 X0))))) ∨ (τ (σ X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1633498 (σ X0)
       have i₂ := eq5318 X0
       grind)
    | exact superpose eq5318 eq1633498
    | exact resolve eq1633498 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1735998 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (σ X0)) (k (τ (σ X0)) (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1735129 X0
       have i₂ := eq32 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq32 eq1735129
    | (have j0 := eq1735129 X0
       grind)
    | exact resolve eq1735129 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735129
  have eq1736321 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op X0 (k X0 (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1735998 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1735998
    | (have j0 := eq1735998 X0
       grind)
    | exact resolve eq1735998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735998
  have eq1736571 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k X0 (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1736321 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1736321
    | (have j0 := eq1736321 X0
       grind)
    | exact resolve eq1736321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736321
  have eq1736755 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op X0 X0))) X0) ∨ (M.op X0 X0) = (M.op X0 (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1736571 X0
       have i₂ := eq32 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq32 eq1736571
    | (have j0 := eq1736571 X0
       grind)
    | exact resolve eq1736571 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1736571
  have eq1736906 : ∀ X0 : G, (τ (σ X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1736755 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1736755
    | (have j0 := eq1736755 X0
       grind)
    | exact resolve eq1736755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736755
  have eq1737020 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k X0 (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1736906 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1736906
    | (have j0 := eq1736906 X0
       grind)
    | exact resolve eq1736906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736906
  have eq1738372 : ∀ X0 : G, (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1737020 (M.op x x)
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq1737020
    | exact resolve eq1737020 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737020
  have eq1743879 : ∀ X0 : G, y = (M.op (M.op y y) y) ∨ (M.op y y) = (k y (M.op y y)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1738372 y
       have i₂ := eq1477509 X0
       grind)
    | exact superpose eq1477509 eq1738372
    | (have j0 := eq1738372 y
       have j1 := eq1477509 X0
       grind)
    | exact resolve eq1738372 eq1477509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477509
  have eq1743880 : ∀ X0 : G, y = (M.op (M.op y y) y) ∨ (M.op y y) = (k y (M.op y y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1738372 y
       have i₂ := eq1477510 X0
       grind)
    | exact superpose eq1477510 eq1738372
    | (have j0 := eq1738372 y
       have j1 := eq1477510 X0
       grind)
    | exact resolve eq1738372 eq1477510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477510
  have eq1743894 : y = (M.op (M.op y y) y) ∨ (M.op y y) = (k y (M.op y y)) ∨ (τ (k y x)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq1738372 y
       have i₂ := eq1505089
       grind)
    | exact superpose eq1505089 eq1738372
    | (have j0 := eq1738372 y
       grind)
    | exact resolve eq1738372 eq1505089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505089
  have eq1743975 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (M.op X0 X0) X0)) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (k (M.op X0 X0) X0) X1 (M.op X0 X0)
       have i₂ := eq1738372 X0
       grind)
    | exact superpose eq1738372 eq25
    | (have j1 := eq1738372 X0
       grind)
    | exact resolve eq25 eq1738372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738372
  have eq1744170 : (M.op y y) = (k y (M.op y y)) ∨ (τ (k y x)) = (τ (M.op x y)) := by
    first
    | (have j1 := eq12 y (M.op y y)
       grind)
    | (have r₁ := eq1743894
       have r₂ := eq12 y (M.op y y)
       grind)
    | exact resolve eq1743894 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743894
  have eq1744184 : ∀ X0 : G, (M.op y y) = (k y (M.op y y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have j0 := eq1743880 X0
       have j1 := eq12 y (M.op y y)
       grind)
    | (have r₁ := eq1743880 X0
       have r₂ := eq12 y (M.op y y)
       grind)
    | exact resolve eq1743880 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743880
  have eq1744185 : ∀ X0 : G, (M.op y y) = (k y (M.op y y)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq1743879 X0
       have j1 := eq12 y (M.op y y)
       grind)
    | (have r₁ := eq1743879 X0
       have r₂ := eq12 y (M.op y y)
       grind)
    | exact resolve eq1743879 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743879
  have eq1744905 : (τ (M.op y y)) = (M.op (τ y) (τ (M.op y y))) ∨ (τ y) = (τ (k (M.op y y) y)) ∨ (τ (k y x)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq1633498 y
       have i₂ := eq1744170
       grind)
    | exact superpose eq1744170 eq1633498
    | (have j0 := eq1633498 y
       grind)
    | exact resolve eq1633498 eq1744170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744170
  have eq1745011 : (τ (k y x)) = (τ (M.op x y)) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have j1 := eq475377 y
       grind)
    | (have r₁ := eq1744905
       have r₂ := eq475377 y
       grind)
    | exact resolve eq1744905 eq475377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744905
  have eq1746153 : (k y x) = (σ (τ (M.op x y))) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq1745011
       grind)
    | exact superpose eq1745011 eq11
    | exact resolve eq11 eq1745011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745011
  have eq1747707 : (M.op x y) = (k y x) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq1746153
       have i₂ := eq11 (M.op x y)
       grind)
    | exact superpose eq11 eq1746153
    | exact resolve eq1746153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746153
  have eq1764258 : ∀ X0 : G, (τ (M.op y y)) = (M.op (τ y) (τ (M.op y y))) ∨ (τ y) = (τ (k (M.op y y) y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1633498 y
       have i₂ := eq1744184 X0
       grind)
    | exact superpose eq1744184 eq1633498
    | (have j0 := eq1633498 y
       have j1 := eq1744184 X0
       grind)
    | exact resolve eq1633498 eq1744184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744184
  have eq1764364 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    intro X0
    first
    | (have j0 := eq1764258 X0
       have j1 := eq475377 y
       grind)
    | (have r₁ := eq1764258 X0
       have r₂ := eq475377 y
       grind)
    | exact resolve eq1764258 eq475377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764258
  have eq1767001 : ∀ X0 : G, (τ (M.op y y)) = (M.op (τ y) (τ (M.op y y))) ∨ (τ y) = (τ (k (M.op y y) y)) ∨ (σ y) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1633498 y
       have i₂ := eq1744185 X0
       grind)
    | exact superpose eq1744185 eq1633498
    | (have j0 := eq1633498 y
       have j1 := eq1744185 X0
       grind)
    | exact resolve eq1633498 eq1744185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633498 eq1744185
  have eq1767107 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    intro X0
    first
    | (have j0 := eq1767001 X0
       have j1 := eq475377 y
       grind)
    | (have r₁ := eq1767001 X0
       have r₂ := eq475377 y
       grind)
    | exact resolve eq1767001 eq475377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475377 eq1767001
  have eq1804133 : (σ x) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k (M.op y y) y)) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq1764364 (M.op (σ y) x)
       have i₂ := eq1767107 x
       grind)
    | exact superpose eq1767107 eq1764364
    | exact resolve eq1764364 eq1767107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764364 eq1767107
  have eq1804372 : (σ x) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k (M.op y y) y)) := by grind
  clear eq1804133
  have eq1807014 : (σ (M.op x y)) ≠ (σ x) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1804372
       grind)
    | exact superpose eq1804372 eq16
    | exact resolve eq16 eq1804372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1807119 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1804372
       grind)
    | exact superpose eq1804372 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1804372
       grind)
    | exact resolve eq13 eq1804372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804372
  have eq1807266 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (τ y) = (τ (k (M.op y y) y)) := by grind
  clear eq1807119
  have eq1807345 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq1807266
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1807266
    | exact resolve eq1807266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807266
  have eq1916932 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (τ y) = (τ (k (M.op y y) y)) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq1807345
       have i₂ := eq1747707
       grind)
    | exact superpose eq1747707 eq1807345
    | exact resolve eq1807345 eq1747707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747707 eq1807345
  have eq1917559 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (τ y) = (τ (k (M.op y y) y)) := by grind
  clear eq1916932
  have eq1917658 : (σ x) = (σ y) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have r₁ := eq1917559
       have r₂ := eq1807014
       grind)
    | exact resolve eq1917559 eq1807014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807014 eq1917559
  have eq1919325 : y = (τ (σ x)) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1917658
       grind)
    | exact superpose eq1917658 eq10
    | exact resolve eq10 eq1917658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917658
  have eq1920005 : x = y ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq1919325
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1919325
    | exact resolve eq1919325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919325
  have eq1920042 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1920005
       grind)
    | exact superpose eq1920005 eq16
    | exact resolve eq16 eq1920005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920005
  have eq1920530 : (τ y) = (τ (k (M.op y y) y)) := by
    first
    | (have r₁ := eq1920042
       have r₂ := eq5318 x
       grind)
    | exact resolve eq1920042 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920042
  have eq1922206 : (k (M.op y y) y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k (M.op y y) y)
       have i₂ := eq1920530
       grind)
    | exact superpose eq1920530 eq11
    | exact resolve eq11 eq1920530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1922210 : ∀ X0 : G, (τ (k (k (M.op y y) y) X0)) = (k (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 (k (M.op y y) y)
       have i₂ := eq1920530
       grind)
    | exact superpose eq1920530 eq43
    | exact resolve eq43 eq1920530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920530
  have eq1923773 : ∀ X0 : G, (τ (k y X0)) = (τ (k (k (M.op y y) y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1922210 X0
       have i₂ := eq43 X0 y
       grind)
    | exact superpose eq43 eq1922210
    | exact resolve eq1922210 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1922210
  have eq1923777 : y = (k (M.op y y) y) := by
    first
    | (have i₁ := eq1922206
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq1922206
    | exact resolve eq1922206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922206
  have eq1923879 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ (M.op y y) = (k y (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq1743975 y X0
       have i₂ := eq1923777
       grind)
    | exact superpose eq1923777 eq1743975
    | (have j0 := eq1743975 y x
       grind)
    | exact resolve eq1743975 eq1923777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743975
  have eq1925672 : ∀ X0 : G, (τ (k y (M.op (k (M.op y y) y) (k (M.op y y) y)))) = (τ (M.op (M.op (k (M.op y y) y) (k (M.op y y) y)) (k (M.op y y) y))) ∨ (k (M.op y y) y) = (M.op (M.op X0 (k (M.op y y) y)) (k (M.op y y) y)) := by
    intro X0
    first
    | (have i₁ := eq1923773 (M.op (k (M.op y y) y) (k (M.op y y) y))
       have i₂ := eq470488 (k (M.op y y) y) X0
       grind)
    | exact superpose eq470488 eq1923773
    | (have j1 := eq470488 (k (M.op y y) y) X0
       grind)
    | exact resolve eq1923773 eq470488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470488 eq1923773
  have eq1927810 : ∀ X0 : G, (τ (k y (M.op y y))) = (τ (M.op (M.op y y) y)) ∨ (k (M.op y y) y) = (M.op (M.op X0 (k (M.op y y) y)) (k (M.op y y) y)) := by
    intro X0
    first
    | (have i₁ := eq1925672 X0
       have i₂ := eq1923777
       grind)
    | exact superpose eq1923777 eq1925672
    | (have j0 := eq1925672 X0
       grind)
    | exact resolve eq1925672 eq1923777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925672
  have eq1927987 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ (τ (k y (M.op y y))) = (τ (M.op (M.op y y) y)) := by
    intro X0
    first
    | (have i₁ := eq1927810 X0
       have i₂ := eq1923777
       grind)
    | exact superpose eq1923777 eq1927810
    | exact resolve eq1927810 eq1923777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923777 eq1927810
  have eq1938058 : y = (M.op y y) ∨ (M.op y y) = (k y (M.op y y)) ∨ (M.op y y) = (k y (M.op y y)) := by
    first
    | (have i₁ := eq1923879 (M.op x y)
       have i₂ := eq1923879 x
       grind)
    | exact superpose eq1923879 eq1923879
    | exact resolve eq1923879 eq1923879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1938137 : y ≠ (M.op y y) ∨ (M.op y y) = (k y (M.op y y)) ∨ (M.op y y) = (k y (M.op y y)) := by
    first
    | (have i₁ := eq474946 y
       have i₂ := eq1923879 y
       grind)
    | exact superpose eq1923879 eq474946
    | (have j0 := eq474946 y
       grind)
    | exact resolve eq474946 eq1923879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474946 eq1923879
  have eq1938332 : y ≠ (M.op y y) ∨ (M.op y y) = (k y (M.op y y)) := by grind
  clear eq1938137
  have eq1938352 : y = (M.op y y) ∨ (M.op y y) = (k y (M.op y y)) := by grind
  clear eq1938058
  have eq1938387 : (M.op y y) = (k y (M.op y y)) := by
    first
    | (have r₁ := eq1938352
       have r₂ := eq1938332
       grind)
    | exact resolve eq1938352 eq1938332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938332 eq1938352
  have eq1938560 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op (M.op y y) y) := by
    first
    | (have i₁ := eq1011 y (M.op y y)
       have i₂ := eq1938387
       grind)
    | exact superpose eq1938387 eq1011
    | (have j0 := eq1011 y (M.op y y)
       grind)
    | (have r₁ := eq1011 y (M.op y y)
       have r₂ := eq1938387
       grind)
    | exact resolve eq1011 eq1938387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1938627 : y = (M.op (M.op y y) y) ∨ (M.op y y) = (M.op (M.op y y) y) := by grind
  clear eq1938560
  have eq1950016 : y ≠ (M.op y y) ∨ (M.op y y) = (M.op (M.op y y) y) := by grind
  clear eq1938627
  have eq2019148 : y = (M.op y y) ∨ (τ (k y (M.op y y))) = (τ (M.op (M.op y y) y)) ∨ (τ (k y (M.op y y))) = (τ (M.op (M.op y y) y)) := by
    first
    | (have i₁ := eq1927987 (M.op x y)
       have i₂ := eq1927987 x
       grind)
    | exact superpose eq1927987 eq1927987
    | exact resolve eq1927987 eq1927987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927987
  have eq2019466 : y = (M.op y y) ∨ (τ (k y (M.op y y))) = (τ (M.op (M.op y y) y)) := by grind
  clear eq2019148
  have eq2019545 : (τ (M.op y y)) = (τ (M.op (M.op y y) y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2019466
       have i₂ := eq1938387
       grind)
    | exact superpose eq1938387 eq2019466
    | exact resolve eq2019466 eq1938387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938387 eq2019466
  have eq2023767 : (M.op (M.op y y) y) = (σ (τ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 (M.op (M.op y y) y)
       have i₂ := eq2019545
       grind)
    | exact superpose eq2019545 eq11
    | exact resolve eq11 eq2019545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019545
  have eq2025365 : (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2023767
       have i₂ := eq11 (M.op y y)
       grind)
    | exact superpose eq11 eq2023767
    | exact resolve eq2023767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023767
  have eq2025374 : (M.op y y) = (M.op (M.op y y) y) := by
    first
    | (have r₁ := eq2025365
       have r₂ := eq1950016
       grind)
    | exact resolve eq2025365 eq1950016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950016 eq2025365
  have eq2025451 : (M.op y y) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq20 y y y
       have i₂ := eq2025374
       grind)
    | exact superpose eq2025374 eq20
    | exact resolve eq20 eq2025374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2025494 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op y y)) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op y y) y
       have i₂ := eq2025374
       grind)
    | exact superpose eq2025374 eq19
    | exact resolve eq19 eq2025374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025374
  have eq2032963 : (M.op y y) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq2025494 y
       have i₂ := eq2025451
       grind)
    | exact superpose eq2025451 eq2025494
    | exact resolve eq2025494 eq2025451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025451 eq2025494
  have eq2033285 : y = (M.op y y) := by
    first
    | (have i₁ := eq2032963
       have i₂ := eq19 y y y
       grind)
    | (have i₁ := eq2032963
       have i₂ := eq19 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq19 eq2032963
    | exact resolve eq2032963 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2032963
  have eq2033469 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1432137
       have i₂ := eq2033285
       grind)
    | exact superpose eq2033285 eq1432137
    | exact resolve eq1432137 eq2033285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432137
  have eq2033635 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5714 y x
       have i₂ := eq2033285
       grind)
    | exact superpose eq2033285 eq5714
    | exact resolve eq5714 eq2033285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5714
  have eq2034030 : ∀ X0 : G, y = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq25 y x y
       have i₂ := eq2033285
       grind)
    | exact superpose eq2033285 eq25
    | exact resolve eq25 eq2033285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq2034192 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2033469
  have eq2039375 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op X0 y) ∨ (τ (k y X0)) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2034030 X0
       have i₂ := eq3497 y X0
       grind)
    | exact superpose eq3497 eq2034030
    | (have j1 := eq3497 y X0
       grind)
    | exact resolve eq2034030 eq3497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497 eq2034030
  have eq2039662 : ∀ X0 : G, (τ (k y X0)) = (τ (M.op X0 y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq2039375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039375
  have eq2102137 : ∀ X0 : G, (k y X0) = (σ (τ (M.op X0 y))) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq11 (k y X0)
       have i₂ := eq2039662 X0
       grind)
    | exact superpose eq2039662 eq11
    | (have j1 := eq2039662 X0
       grind)
    | exact resolve eq11 eq2039662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039662
  have eq2103747 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq2102137 X0
       have i₂ := eq11 (M.op X0 y)
       grind)
    | exact superpose eq11 eq2102137
    | (have j0 := eq2102137 X0
       grind)
    | exact resolve eq2102137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102137
  have eq2169934 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2034192
       grind)
    | exact superpose eq2034192 eq16
    | exact resolve eq16 eq2034192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2169988 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq359556 x (σ y)
       have i₂ := eq2034192
       grind)
    | exact superpose eq2034192 eq359556
    | exact resolve eq359556 eq2034192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359556 eq2034192
  have eq2170340 : (τ (σ y)) = (k (τ (σ (M.op y y))) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2169988
       have i₂ := eq5318 y
       grind)
    | exact superpose eq5318 eq2169988
    | exact resolve eq2169988 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169988
  have eq2170405 : (τ (σ y)) = (k (M.op y y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2170340
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq2170340
    | exact resolve eq2170340 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170340
  have eq2170440 : (k y x) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2170405
       have i₂ := eq2033285
       grind)
    | exact superpose eq2033285 eq2170405
    | exact resolve eq2170405 eq2033285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033285 eq2170405
  have eq2170463 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2170440
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2170440
    | exact resolve eq2170440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170440
  have eq2171530 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2103747 x
       have i₂ := eq2170463
       grind)
    | exact superpose eq2170463 eq2103747
    | (have j0 := eq2103747 x
       grind)
    | exact resolve eq2103747 eq2170463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103747 eq2170463
  have eq2171724 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2171530
  have eq2173264 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2169934
       have i₂ := eq2171724
       grind)
    | exact superpose eq2171724 eq2169934
    | exact resolve eq2169934 eq2171724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169934 eq2171724
  have eq2173274 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2173264
  have eq2173275 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2173274
  have eq2173383 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2033635 (σ x)
       have i₂ := eq2173275
       grind)
    | exact superpose eq2173275 eq2033635
    | exact resolve eq2033635 eq2173275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033635
  have eq2173740 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2173383
       have i₂ := eq2173275
       grind)
    | exact superpose eq2173275 eq2173383
    | exact resolve eq2173383 eq2173275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173275 eq2173383
  have eq2176826 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2173740
       grind)
    | exact superpose eq2173740 eq10
    | exact resolve eq10 eq2173740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173740
  have eq2177628 : x = y := by
    first
    | (have i₁ := eq2176826
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2176826
    | exact resolve eq2176826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176826
  have eq2177822 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2177628
       grind)
    | exact superpose eq2177628 eq16
    | exact resolve eq16 eq2177628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177628
  have eq2178498 : False := by grind
  exact eq2178498

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq62 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq68 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq62 X2 X0 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X1 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X2 (M.op X0 X1))
       have i₂ := eq68 X1 X2 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq98 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq102 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq105 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq131 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq136 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq98 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq444 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq435 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq435
    | (have j0 := eq435 (τ X0)
       grind)
    | exact resolve eq435 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq435
  have eq445 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq444 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq444
    | (have j0 := eq444 X0
       grind)
    | exact resolve eq444 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq448 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq445 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq445
    | (have j0 := eq445 X0
       grind)
    | exact resolve eq445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq480 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq12
    | (have j1 := eq105 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq105 X0
       grind)
    | exact resolve eq12 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq500 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq489 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq501 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq500 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq500
    | (have j0 := eq500 X0
       grind)
    | exact resolve eq500 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq502 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq480 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq480
    | (have j0 := eq480 X0
       grind)
    | exact resolve eq480 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq508 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq502 X0
       grind)
    | exact superpose eq502 eq12
    | (have j1 := eq502 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq502 X0
       grind)
    | exact resolve eq12 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq508 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq538 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq527 X0
       grind)
    | exact superpose eq527 eq10
    | (have j1 := eq527 X0
       grind)
    | exact resolve eq10 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (τ (k X1 (σ (M.op X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (k X0 X0)
       have i₂ := eq527 X0
       grind)
    | exact superpose eq527 eq23
    | (have j1 := eq527 X0
       grind)
    | exact resolve eq23 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq565 : ∀ X0 X1 : G, (k (τ X1) (k X0 X0)) = (k (τ X1) (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 X1
       have i₂ := eq23 X1 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq545
    | (have j0 := eq545 X0 X1
       grind)
    | exact resolve eq545 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq572 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq538 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq538
    | (have j0 := eq538 X0
       grind)
    | exact resolve eq538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq590 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131 x y
       grind)
    | exact superpose eq131 eq16
    | (have j1 := eq131 x y
       grind)
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq631 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq572 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq903 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq501 X0
       grind)
    | exact superpose eq501 eq11
    | (have j1 := eq501 X0
       grind)
    | exact resolve eq11 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq905 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq903 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq903
    | (have j0 := eq903 X0
       grind)
    | exact resolve eq903 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq952 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq905 X0
       grind)
    | exact superpose eq905 eq10
    | (have j1 := eq905 X0
       grind)
    | exact resolve eq10 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq997 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ X0) = (M.op (M.op X1 (τ X0)) (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (τ X0) (τ X0)
       have i₂ := eq952 X0
       grind)
    | exact superpose eq952 eq62
    | (have j1 := eq952 X0
       grind)
    | exact resolve eq62 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ X0) = (M.op (τ (k X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ X0) (τ X0) X1
       have i₂ := eq952 X0
       grind)
    | exact superpose eq952 eq62
    | (have j1 := eq952 X0
       grind)
    | exact resolve eq62 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1623 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq997 (σ X0) X1
       grind)
    | exact superpose eq997 eq29
    | (have j1 := eq997 (σ X0) X1
       grind)
    | exact resolve eq29 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1637 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1623 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1623
    | (have j0 := eq1623 X0 X1
       grind)
    | exact resolve eq1623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1655 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X1 (τ (σ X0))) (k (τ (σ X0)) X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1637 X0 X1
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq1637
    | (have j0 := eq1637 X0 X1
       grind)
    | exact resolve eq1637 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq1672 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1655 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1655
    | (have j0 := eq1655 X0 X1
       grind)
    | exact resolve eq1655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq1698 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0
       have i₂ := eq1672 X0 X1
       grind)
    | exact superpose eq1672 eq448
    | (have j0 := eq448 X0
       have j1 := eq1672 X0 X1
       grind)
    | (have r₁ := eq448 X0
       have r₂ := eq1672 X0 X1
       grind)
    | exact resolve eq448 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1719 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1789 : ∀ X0 X2 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq62 (M.op x X0) (k X0 X0) X2
       have i₂ := eq1719 X0 x
       grind)
    | exact superpose eq1719 eq62
    | (have j1 := eq1719 X0 x
       grind)
    | exact resolve eq62 eq1719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1926 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (k (σ X0) (σ X0))) (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq998 (σ X0) X1
       grind)
    | exact superpose eq998 eq29
    | (have j1 := eq998 (σ X0) X1
       grind)
    | exact resolve eq29 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq998
  have eq1940 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (k (σ X0) (σ X0))) (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1926 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1926
    | (have j0 := eq1926 X0 X1
       grind)
    | exact resolve eq1926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq1958 : ∀ X0 X1 : G, (M.op (τ (k (σ X0) (σ X0))) (M.op X0 X1)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1940 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1940
    | (have j0 := eq1940 X0 X1
       grind)
    | exact resolve eq1940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq1975 : ∀ X0 X1 : G, (M.op (k (τ (σ X0)) X0) (M.op X0 X1)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1958 X0 X1
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq1958
    | (have j0 := eq1958 X0 X1
       grind)
    | exact resolve eq1958 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1958
  have eq1990 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1975 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1975
    | (have j0 := eq1975 X0 X1
       grind)
    | exact resolve eq1975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq2024 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1990 X0 (M.op (k X0 X0) x)
       have i₂ := eq1789 X0 x
       grind)
    | exact superpose eq1789 eq1990
    | (have j0 := eq1990 X0 x
       have j1 := eq1789 X0 x
       grind)
    | exact resolve eq1990 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq2038 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (k X0 X0) (M.op X0 x)
       have i₂ := eq1990 X0 x
       grind)
    | exact superpose eq1990 eq62
    | (have j1 := eq1990 X0 X1
       grind)
    | exact resolve eq62 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq2059 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2024 X0
       have j1 := eq631 X0
       grind)
    | (have r₁ := eq2024 X0
       have r₂ := eq631 X0
       grind)
    | exact resolve eq2024 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2095 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ X0) = (σ (k (k X0 X0) (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq502 (k X0 X0)
       have i₂ := eq2059 X0
       grind)
    | exact superpose eq2059 eq502
    | (have j1 := eq2059 X0
       grind)
    | exact resolve eq502 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq2059
  have eq2096 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095
  have eq2224 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1719 X0 (M.op x (k X0 X0))
       have i₂ := eq2038 X0 x
       grind)
    | exact superpose eq2038 eq1719
    | (have j0 := eq1719 X0 x
       have j1 := eq2038 X0 x
       grind)
    | exact resolve eq1719 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719 eq2038
  have eq2229 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2224 X0
       have j1 := eq448 X0
       grind)
    | (have r₁ := eq2224 X0
       have r₂ := eq448 X0
       grind)
    | exact resolve eq2224 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq2224
  have eq2441 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) (k X0 X0))
       have i₂ := eq2096 X0
       grind)
    | exact superpose eq2096 eq10
    | (have j1 := eq2096 X0
       grind)
    | exact resolve eq10 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq2481 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2441 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2441
    | (have j0 := eq2441 X0
       grind)
    | exact resolve eq2441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441
  have eq2487 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq2542 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2487 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq4365 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136
    | exact resolve eq136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq4432 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4365 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4365
    | (have j0 := eq4365 X0 X1
       grind)
    | exact resolve eq4365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq13171 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq565
    | (have j0 := eq565 X1 X1
       grind)
    | exact resolve eq565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq13235 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (k X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2229 X1
       have i₂ := eq13171 X0 X1
       grind)
    | exact superpose eq13171 eq2229
    | (have j0 := eq2229 X0
       have j1 := eq13171 X1 X0
       grind)
    | exact resolve eq2229 eq13171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229 eq13171
  have eq13290 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13235 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13235
  have eq13497 : ∀ X0 : G, (k (k X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2481 X0
       have i₂ := eq13290 X0 (k X0 X0)
       grind)
    | exact superpose eq13290 eq2481
    | (have j0 := eq2481 X0
       have j1 := eq13290 X0 x
       grind)
    | exact resolve eq2481 eq13290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481 eq13290
  have eq13517 : ∀ X0 : G, (k (k X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13497 X0
       have j1 := eq631 X0
       grind)
    | (have r₁ := eq13497 X0
       have r₂ := eq631 X0
       grind)
    | exact resolve eq13497 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq13497
  have eq13643 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13517 (M.op X0 X0)
       have i₂ := eq2542 X0
       grind)
    | exact superpose eq2542 eq13517
    | (have j1 := eq2542 X0
       grind)
    | exact resolve eq13517 eq2542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542 eq13517
  have eq13699 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13643
  have eq13734 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq13699 X0
       have j1 := eq95 X0 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13699 x
       have r₂ := eq95 x x x
       grind)
    | exact resolve eq13699 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq13699
  have eq13768 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13734 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq13734 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq13734
    | exact resolve eq13734 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13734
  have eq13904 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq13768 (σ X0)
       grind)
    | exact superpose eq13768 eq15
    | exact resolve eq15 eq13768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13934 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13904 X0
       have i₂ := eq13768 X0
       grind)
    | exact superpose eq13768 eq13904
    | exact resolve eq13904 eq13768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13768 eq13904
  have eq18743 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq603 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq603
    | (have j0 := eq603 (τ X0) (τ X1)
       grind)
    | exact resolve eq603 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq18770 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18743 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq18743
    | (have j0 := eq18743 X0 X1
       grind)
    | exact resolve eq18743 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18743
  have eq18779 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18770 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18770
    | (have j0 := eq18770 X0 X1
       grind)
    | exact resolve eq18770 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18770
  have eq18785 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18779 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18779
    | (have j0 := eq18779 X0 X1
       grind)
    | exact resolve eq18779 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18779
  have eq18788 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18785 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18785
    | (have j0 := eq18785 X0 X1
       grind)
    | exact resolve eq18785 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18785
  have eq18791 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18788 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18788
    | (have j0 := eq18788 X0 X1
       grind)
    | exact resolve eq18788 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18788
  have eq18794 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18791 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18791
    | (have j0 := eq18791 X0 X1
       grind)
    | exact resolve eq18791 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18791
  have eq51101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq590
       have i₂ := eq4432 x y
       grind)
    | exact superpose eq4432 eq590
    | (have j1 := eq4432 (σ x) (σ y)
       grind)
    | (have r₁ := eq590
       have r₂ := eq4432 x y
       grind)
    | (have r₁ := eq590
       have r₂ := eq4432 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq590
       have r₂ := eq4432 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq590 eq4432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq4432
  have eq51102 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq51101
  have eq282170 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51102
       grind)
    | exact superpose eq51102 eq16
    | exact resolve eq16 eq51102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51102
  have eq282171 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq282170
       have r₂ := eq13934 x
       grind)
    | exact resolve eq282170 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282170
  have eq282174 : y ≠ y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq282171
       grind)
    | exact superpose eq282171 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq282171
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq282171
       grind)
    | exact resolve eq12 eq282171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282176 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62 x y X0
       have i₂ := eq282171
       grind)
    | exact superpose eq282171 eq62
    | exact resolve eq62 eq282171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282171
  have eq282219 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq282174
  have eq282333 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq282176 (M.op y x)
       have i₂ := eq282176 x
       grind)
    | exact superpose eq282176 eq282176
    | exact resolve eq282176 eq282176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282176
  have eq282392 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq282333
  have eq282460 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq62 (σ x) (σ y) X0
       have i₂ := eq282392
       grind)
    | exact superpose eq282392 eq62
    | exact resolve eq62 eq282392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq282392
  have eq294926 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq603 x y
       have i₂ := eq282219
       grind)
    | exact superpose eq282219 eq603
    | (have j0 := eq603 x y
       grind)
    | exact resolve eq603 eq282219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq282219
  have eq294943 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq294926
  have eq295246 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq282460 (M.op (σ y) x)
       have i₂ := eq282460 x
       grind)
    | exact superpose eq282460 eq282460
    | exact resolve eq282460 eq282460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282460
  have eq295354 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq295246
  have eq295392 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq295354
       have i₂ := eq13934 y
       grind)
    | exact superpose eq13934 eq295354
    | exact resolve eq295354 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295354
  have eq295418 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq295392
       grind)
    | exact superpose eq295392 eq10
    | exact resolve eq10 eq295392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295392
  have eq295658 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq295418
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq295418
    | exact resolve eq295418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295418
  have eq295725 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq295658
       grind)
    | exact superpose eq295658 eq16
    | exact resolve eq16 eq295658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295658
  have eq295801 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq295725
       have r₂ := eq13934 x
       grind)
    | exact resolve eq295725 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295725
  have eq295852 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq295801
       grind)
    | exact superpose eq295801 eq10
    | exact resolve eq10 eq295801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295801
  have eq296139 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq295852
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq295852
    | exact resolve eq295852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295852
  have eq296140 : y = (M.op y y) := by grind
  clear eq296139
  have eq296216 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq294943
       have i₂ := eq296140
       grind)
    | exact superpose eq296140 eq294943
    | exact resolve eq294943 eq296140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294943
  have eq296367 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq296216
  have eq300589 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq296367
       grind)
    | exact superpose eq296367 eq16
    | exact resolve eq16 eq296367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300638 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq296367
       grind)
    | exact superpose eq296367 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq296367
       grind)
    | exact resolve eq12 eq296367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296367
  have eq300686 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq300638
  have eq300706 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq300686
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq300686
    | exact resolve eq300686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300686
  have eq300748 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq300706
       have i₂ := eq13934 y
       grind)
    | exact superpose eq13934 eq300706
    | exact resolve eq300706 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300706
  have eq300763 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq300748
       have i₂ := eq296140
       grind)
    | exact superpose eq296140 eq300748
    | exact resolve eq300748 eq296140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296140 eq300748
  have eq300782 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq300763
       grind)
    | exact superpose eq300763 eq10
    | exact resolve eq10 eq300763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300763
  have eq301046 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq300782
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq300782
    | exact resolve eq300782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300782
  have eq301148 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq301046
       grind)
    | exact superpose eq301046 eq16
    | exact resolve eq16 eq301046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301046
  have eq301233 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq301148
       have r₂ := eq13934 x
       grind)
    | exact resolve eq301148 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301148
  have eq301263 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq301233
       grind)
    | exact superpose eq301233 eq10
    | exact resolve eq10 eq301233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301233
  have eq301503 : y = (k y x) := by
    first
    | (have i₁ := eq301263
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq301263
    | exact resolve eq301263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301263
  have eq301615 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18794 y x
       have i₂ := eq301503
       grind)
    | exact superpose eq301503 eq18794
    | (have j0 := eq18794 x y
       grind)
    | (have r₁ := eq18794 y x
       have r₂ := eq301503
       grind)
    | exact resolve eq18794 eq301503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18794 eq301503
  have eq301627 : y = (M.op x y) ∨ x = y := by grind
  clear eq301615
  have eq301643 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq300589
       have i₂ := eq301627
       grind)
    | exact superpose eq301627 eq300589
    | exact resolve eq300589 eq301627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300589 eq301627
  have eq301710 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq301643
  have eq301734 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq301710
       grind)
    | exact superpose eq301710 eq16
    | exact resolve eq16 eq301710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301710
  have eq301823 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq301734
       have r₂ := eq13934 x
       grind)
    | exact resolve eq301734 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301734
  have eq301828 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq301823
       grind)
    | exact superpose eq301823 eq16
    | exact resolve eq16 eq301823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301836 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq301823
       grind)
    | exact superpose eq301823 eq10
    | exact resolve eq10 eq301823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301823
  have eq302100 : x = y := by
    first
    | (have i₁ := eq301836
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq301836
    | exact resolve eq301836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301836
  have eq302103 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq301828
       have i₂ := eq13934 x
       grind)
    | exact superpose eq13934 eq301828
    | exact resolve eq301828 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13934 eq301828
  have eq302167 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq302103
       have i₂ := eq302100
       grind)
    | exact superpose eq302100 eq302103
    | exact resolve eq302103 eq302100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302100 eq302103
  have eq302168 : False := by grind
  exact eq302168

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq353 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = X1 ∨ (k (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x x) X1
       have i₂ := eq61 x x x
       grind)
    | exact superpose eq61 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq13 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq354 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq354 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq354 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq366 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq355 (σ X0)
       grind)
    | exact superpose eq355 eq15
    | exact resolve eq15 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq355 (τ X0)
       grind)
    | exact superpose eq355 eq31
    | exact resolve eq31 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq372
    | exact resolve eq372 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq366 X0
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq366
    | exact resolve eq366 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq366
  have eq431 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq61
    | exact resolve eq61 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq61
    | exact resolve eq61 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq722 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq3031 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq722 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq722
    | exact resolve eq722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq3142 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3031 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3031
    | (have j0 := eq3031 X0 X1
       grind)
    | exact resolve eq3031 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3031
  have eq3148 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3142 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq3142 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq3142 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3142
  have eq3149 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3148 X0 X1
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq3148
    | (have j0 := eq3148 X0 X1
       grind)
    | exact resolve eq3148 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3148
  have eq3150 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3149 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3149
    | (have j0 := eq3149 X0 X1
       grind)
    | exact resolve eq3149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq3151 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3150 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3150
    | exact resolve eq3150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3175 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq3150 X0 X1
       grind)
    | exact superpose eq3150 eq22
    | (have j1 := eq3150 X0 X1
       grind)
    | exact resolve eq22 eq3150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3176 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3150 (σ X0) X1
       grind)
    | exact superpose eq3150 eq15
    | (have j1 := eq3150 (σ X0) X1
       grind)
    | exact resolve eq15 eq3150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3150
  have eq3221 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3176 X0 X1
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq3176
    | (have j0 := eq3176 X0 X1
       grind)
    | exact resolve eq3176 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176
  have eq3239 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq3151 (τ X1) X0
       grind)
    | exact superpose eq3151 eq18
    | (have j1 := eq3151 (τ X1) X0
       grind)
    | exact resolve eq18 eq3151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3151
  have eq3419 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) (M.op X0 X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3175 (M.op X1 (σ X0)) (M.op X0 X0)
       have i₂ := eq431 X0 X1
       grind)
    | exact superpose eq431 eq3175
    | exact resolve eq3175 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175
  have eq3477 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3419 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3419
    | (have j0 := eq3419 X0 X1
       grind)
    | exact resolve eq3419 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq3584 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3239 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3239
    | exact resolve eq3239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq3649 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3584 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3584
    | (have j0 := eq3584 X0 X1
       grind)
    | exact resolve eq3584 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3584
  have eq4055 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3221 x y
       grind)
    | exact superpose eq3221 eq16
    | (have j1 := eq3221 x y
       grind)
    | exact resolve eq16 eq3221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4058 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (k X0 X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 (σ X1)
       have i₂ := eq3221 X0 X1
       grind)
    | exact superpose eq3221 eq432
    | (have j1 := eq3221 X0 X1
       grind)
    | exact resolve eq432 eq3221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq4108 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3221 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4055
       have i₂ := eq3649 y x
       grind)
    | exact superpose eq3649 eq4055
    | (have j1 := eq3649 y x
       grind)
    | (have r₁ := eq4055
       have r₂ := eq3649 y x
       grind)
    | exact resolve eq4055 eq3649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3649
  have eq4145 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4144
  have eq4153 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq4145
       grind)
    | exact superpose eq4145 eq61
    | exact resolve eq61 eq4145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4145
  have eq4193 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k (M.op X0 X0) X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4108 (M.op x x) X1
       have i₂ := eq61 x x x
       grind)
    | exact superpose eq61 eq4108
    | exact resolve eq4108 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq5782 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) ∨ (k (M.op X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 (M.op X0 X1)
       have i₂ := eq61 X0 X0 X1
       grind)
    | exact superpose eq61 eq353
    | (have j0 := eq353 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq353 x (M.op x x)
       have r₂ := eq61 x x x
       grind)
    | exact resolve eq353 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq5805 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5782 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5782
  have eq5910 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4193 X0 (M.op X0 X1)
       have i₂ := eq5805 X0 X1
       grind)
    | exact superpose eq5805 eq4193
    | (have j0 := eq4193 X0 (M.op X0 X1)
       have j1 := eq5805 X0 X1
       grind)
    | exact resolve eq4193 eq5805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq5922 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5910 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5910
  have eq11184 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (M.op (τ X0) (τ X0))) (σ (τ (k X0 X1)))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4058 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq4058
    | (have j0 := eq4058 (τ X0) (τ X1)
       grind)
    | exact resolve eq4058 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4058
  have eq11279 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (M.op (τ X0) (τ X0))) (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11184 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11184
    | (have j0 := eq11184 X0 X1
       grind)
    | exact resolve eq11184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11184
  have eq11320 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (M.op X0 X0))) (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11279 X0 X1
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq11279
    | (have j0 := eq11279 X0 X1
       grind)
    | exact resolve eq11279 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11279
  have eq11352 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11320 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq11320
    | (have j0 := eq11320 X0 X1
       grind)
    | exact resolve eq11320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11320
  have eq11374 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (k X0 X1)) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11352 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11352
    | (have j0 := eq11352 X0 X1
       grind)
    | exact resolve eq11352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11352
  have eq11396 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op (M.op X0 X0) (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11374 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11374
    | (have j0 := eq11374 X0 X1
       grind)
    | exact resolve eq11374 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11374
  have eq11413 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (M.op X0 X0) (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11396 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11396
    | (have j0 := eq11396 X0 X1
       grind)
    | exact resolve eq11396 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11396
  have eq11427 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op (M.op X0 X0) (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11413 X0 X1
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq11413
    | (have j0 := eq11413 X0 X1
       grind)
    | exact resolve eq11413 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11413
  have eq11440 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (k X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11427 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq11427
    | (have j0 := eq11427 X0 X1
       grind)
    | exact resolve eq11427 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11427
  have eq11454 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (k (M.op X0 X0) X1)) ∨ (M.op (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11440 (M.op x x) X1
       have i₂ := eq61 x x x
       grind)
    | exact superpose eq61 eq11440
    | (have j0 := eq11440 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq11440 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11440
  have eq26243 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X1 X0)) (M.op (τ X0) (τ X0))) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3477 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3477
    | exact resolve eq3477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477
  have eq26450 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X1 X0)) (τ (M.op X0 X0))) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26243 X0 X1
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq26243
    | (have j0 := eq26243 X0 X1
       grind)
    | exact resolve eq26243 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq26243
  have eq26475 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = X0 ∨ (τ X0) = (τ (k (M.op X1 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26450 X0 X1
       have i₂ := eq31 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact superpose eq31 eq26450
    | (have j0 := eq26450 X0 X1
       grind)
    | exact resolve eq26450 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq26450
  have eq26587 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X1 X0) (M.op X0 X0))) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (M.op X1 X0) X1
       have i₂ := eq26475 X0 X1
       grind)
    | exact superpose eq26475 eq67
    | (have j1 := eq26475 X0 X1
       grind)
    | exact resolve eq67 eq26475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26475
  have eq26920 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X1 X0) (M.op X0 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (M.op X1 X0) (M.op X0 X0))
       have i₂ := eq26587 X0 X1
       grind)
    | exact superpose eq26587 eq11
    | (have j1 := eq26587 X0 X1
       grind)
    | exact resolve eq11 eq26587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26587
  have eq27074 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26920 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26920
    | (have j0 := eq26920 X0 X1
       grind)
    | exact resolve eq26920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26920
  have eq27299 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 (M.op X0 X0)) X0) ∨ (M.op X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27074 (M.op x x) X1
       have i₂ := eq61 x x x
       grind)
    | exact superpose eq61 eq27074
    | exact resolve eq27074 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27074
  have eq49372 : y = (M.op y (M.op (M.op x x) (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op (M.op x x) (M.op x x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5922 (M.op x x) (M.op y x)
       have i₂ := eq4153 x
       grind)
    | exact superpose eq4153 eq5922
    | exact resolve eq5922 eq4153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4153 eq5922
  have eq49842 : y = (M.op y x) ∨ (σ (M.op x x)) = (M.op (σ (M.op (M.op x x) (M.op x x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq49372
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq49372
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq49372
    | exact resolve eq49372 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49372
  have eq49896 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq49842
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq49842
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq49842
    | exact resolve eq49842 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49842
  have eq49897 : y = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq49896
  have eq49984 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq49897
       grind)
    | exact superpose eq49897 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq49897
       grind)
    | exact resolve eq12 eq49897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49897
  have eq50049 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq49984
  have eq50615 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4055
       have i₂ := eq50049
       grind)
    | exact superpose eq50049 eq4055
    | exact resolve eq4055 eq50049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4055 eq50049
  have eq50653 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq50615
  have eq50654 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq50653
  have eq50660 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50654
       grind)
    | exact superpose eq50654 eq16
    | exact resolve eq16 eq50654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50663 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq431 y (σ x)
       have i₂ := eq50654
       grind)
    | exact superpose eq50654 eq431
    | exact resolve eq431 eq50654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq50654
  have eq50880 : (σ y) = (σ (k (M.op x x) (M.op y y))) ∨ (σ y) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq3221 (M.op x x) (M.op y y)
       have i₂ := eq50663
       grind)
    | exact superpose eq50663 eq3221
    | exact resolve eq3221 eq50663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221
  have eq51024 : (σ x) = (σ y) ∨ (σ y) = (σ (k (M.op x x) (M.op y y))) := by
    first
    | (have i₁ := eq50880
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq50880
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq50880
    | exact resolve eq50880 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50880
  have eq52023 : y = (τ (σ x)) ∨ (σ y) = (σ (k (M.op x x) (M.op y y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq51024
       grind)
    | exact superpose eq51024 eq10
    | exact resolve eq10 eq51024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51024
  have eq52124 : x = y ∨ (σ y) = (σ (k (M.op x x) (M.op y y))) := by
    first
    | (have i₁ := eq52023
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52023
    | exact resolve eq52023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52023
  have eq52145 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k (M.op x x) (M.op y y))) := by
    first
    | (have i₁ := eq50660
       have i₂ := eq52124
       grind)
    | exact superpose eq52124 eq50660
    | exact resolve eq50660 eq52124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52124
  have eq52150 : (σ y) = (σ (k (M.op x x) (M.op y y))) := by grind
  clear eq52145
  have eq52175 : (k (M.op x x) (M.op y y)) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k (M.op x x) (M.op y y))
       have i₂ := eq52150
       grind)
    | exact superpose eq52150 eq10
    | exact resolve eq10 eq52150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52150
  have eq52276 : y = (k (M.op x x) (M.op y y)) := by
    first
    | (have i₁ := eq52175
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq52175
    | exact resolve eq52175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52175
  have eq52301 : (M.op x y) = (M.op x x) ∨ x = (M.op (M.op x x) (M.op y y)) := by
    first
    | (have i₁ := eq11454 x (M.op y y)
       have i₂ := eq52276
       grind)
    | exact superpose eq52276 eq11454
    | (have j0 := eq11454 x (M.op y y)
       grind)
    | exact resolve eq11454 eq52276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11454 eq52276
  have eq54943 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op (M.op x x) (M.op y y)) := by
    first
    | (have i₁ := eq50660
       have i₂ := eq52301
       grind)
    | exact superpose eq52301 eq50660
    | exact resolve eq50660 eq52301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52301
  have eq55008 : x = (M.op (M.op x x) (M.op y y)) := by grind
  clear eq54943
  have eq55023 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq67 y (M.op x x) y
       have i₂ := eq55008
       grind)
    | exact superpose eq55008 eq67
    | exact resolve eq67 eq55008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq55028 : x = y ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq27299 y (M.op x x)
       have i₂ := eq55008
       grind)
    | exact superpose eq55008 eq27299
    | exact resolve eq27299 eq55008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27299 eq55008
  have eq55193 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq50663
       have i₂ := eq55023
       grind)
    | exact superpose eq55023 eq50663
    | exact resolve eq50663 eq55023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50663
  have eq55971 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq50660
       have i₂ := eq55028
       grind)
    | exact superpose eq55028 eq50660
    | exact resolve eq50660 eq55028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55028
  have eq55992 : (k x y) = (M.op y y) := by grind
  clear eq55971
  have eq56007 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq55992
       have i₂ := eq55023
       grind)
    | exact superpose eq55023 eq55992
    | exact resolve eq55992 eq55023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55023 eq55992
  have eq56919 : (σ (M.op x x)) = (k (M.op (σ (M.op x x)) (σ (M.op x x))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq5805 (σ (M.op x x)) (σ (M.op x y))
       have i₂ := eq55193
       grind)
    | exact superpose eq55193 eq5805
    | exact resolve eq5805 eq55193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5805 eq55193
  have eq57010 : (σ (M.op x x)) = (k (σ (M.op (M.op x x) (M.op x x))) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq56919
       have i₂ := eq385 (M.op x x)
       grind)
    | exact superpose eq385 eq56919
    | exact resolve eq56919 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56919
  have eq57069 : (σ (M.op x x)) = (σ (k (M.op (M.op x x) (M.op x x)) y)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq57010
       have i₂ := eq15 (M.op (M.op x x) (M.op x x)) y
       grind)
    | exact superpose eq15 eq57010
    | exact resolve eq57010 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57010
  have eq57110 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq57069
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq57069
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq57069
    | exact resolve eq57069 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57069
  have eq57141 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq57110
       have i₂ := eq56007
       grind)
    | exact superpose eq56007 eq57110
    | exact resolve eq57110 eq56007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57110
  have eq57154 : (σ y) = (M.op (σ y) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    first
    | (have r₁ := eq57141
       have r₂ := eq50660
       grind)
    | exact resolve eq57141 eq50660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50660 eq57141
  have eq57166 : (σ y) = (M.op (σ y) (σ (M.op (M.op x x) (M.op x x)))) := by
    first
    | (have i₁ := eq57154
       have i₂ := eq385 (M.op x x)
       grind)
    | exact superpose eq385 eq57154
    | exact resolve eq57154 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq57154
  have eq57169 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq57166
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq57166
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq57166
    | exact resolve eq57166 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq57166
  have eq57210 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq57169
       grind)
    | exact superpose eq57169 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq57169
       grind)
    | exact resolve eq12 eq57169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57169
  have eq57277 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq57210
  have eq57325 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq57277
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq57277
    | exact resolve eq57277 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57277
  have eq57394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57325
       have i₂ := eq56007
       grind)
    | exact superpose eq56007 eq57325
    | exact resolve eq57325 eq56007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56007 eq57325
  have eq57451 : False := by grind
  exact eq57451

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  clear eq18
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
  have eq368 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq368 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq368 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq368 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq380 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq369 (σ X0)
       grind)
    | exact superpose eq369 eq15
    | exact resolve eq15 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq369 (τ X0)
       grind)
    | exact superpose eq369 eq31
    | exact resolve eq31 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq393 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq386 X0
       have i₂ := eq369 X0
       grind)
    | exact superpose eq369 eq386
    | exact resolve eq386 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq399 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq380 X0
       have i₂ := eq369 X0
       grind)
    | exact superpose eq369 eq380
    | exact resolve eq380 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq380
  have eq445 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq399 X0
       grind)
    | exact superpose eq399 eq61
    | exact resolve eq61 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (σ X0) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       have i₂ := eq445 X0 X1
       grind)
    | exact superpose eq445 eq12
    | exact resolve eq12 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       have i₂ := eq445 X0 X1
       grind)
    | exact superpose eq445 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (M.op X1 (σ X0))
       grind)
    | exact resolve eq13 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq514 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq503 X0 X1
       have i₂ := eq399 (M.op X0 X0)
       grind)
    | exact superpose eq399 eq503
    | (have j0 := eq503 X0 X1
       grind)
    | exact resolve eq503 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq521 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq514 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq514
    | (have j0 := eq514 X0 X1
       grind)
    | exact resolve eq514 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq522 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq521 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq525 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1
       have i₂ := eq399 (M.op X0 X0)
       grind)
    | exact superpose eq399 eq522
    | (have j0 := eq522 X0 X1
       grind)
    | exact resolve eq522 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq526 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq61 X0 X0 X0
       grind)
    | (have i₁ := eq525 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq61 eq525
    | (have j0 := eq525 X0 X1
       grind)
    | exact resolve eq525 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq527 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq526 X0 X1
       have j1 := eq502 X0 X1
       grind)
    | (have r₁ := eq526 X0 X1
       have r₂ := eq502 X0 X1
       grind)
    | exact resolve eq526 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq526
  have eq576 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X0) (M.op X1 (σ X0))
       have i₂ := eq527 X0 X1
       grind)
    | exact superpose eq527 eq28
    | exact resolve eq28 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq577 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq576
    | exact resolve eq576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq631 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq655 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq631 X0 X1
       have i₂ := eq399 X1
       grind)
    | exact superpose eq399 eq631
    | (have j0 := eq631 X0 X1
       grind)
    | exact resolve eq631 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq662 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X0)) (τ (M.op X1 (σ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq577 (σ X0) X1
       have i₂ := eq399 X0
       grind)
    | exact superpose eq399 eq577
    | exact resolve eq577 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq1279 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X0 X0) (τ (τ (M.op X1 (σ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X0) (τ (M.op X1 (σ (σ X0))))
       have i₂ := eq662 X0 X1
       grind)
    | exact superpose eq662 eq28
    | exact resolve eq28 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq662
  have eq1283 : ∀ X0 X1 : G, (k (M.op X0 X0) (τ (τ (M.op X1 (σ (σ X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1279 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1279
    | exact resolve eq1279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq2208 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq655 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq655
    | exact resolve eq655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq2302 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2208 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2208
    | (have j0 := eq2208 X0 X1
       grind)
    | exact resolve eq2208 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2208
  have eq2315 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq2302 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq2302 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq2302 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq2302 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302
  have eq2323 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2315 X0 X1
       have i₂ := eq393 X0
       grind)
    | exact superpose eq393 eq2315
    | (have j0 := eq2315 X0 X1
       grind)
    | exact resolve eq2315 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315
  have eq2327 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2323 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2323
    | (have j0 := eq2323 X0 X1
       grind)
    | exact resolve eq2323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2449 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2327 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2327
    | exact resolve eq2327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327
  have eq3342 : ∀ X0 X1 : G, (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X1 X0
       have i₂ := eq2449 (τ (M.op X0 (σ X1))) (M.op X1 X1)
       grind)
    | exact superpose eq2449 eq577
    | (have j1 := eq2449 (τ (M.op X0 (σ X1))) (M.op X1 X1)
       grind)
    | exact resolve eq577 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq3343 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1283 X1 X0
       have i₂ := eq2449 (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)
       grind)
    | exact superpose eq2449 eq1283
    | (have j1 := eq2449 (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)
       grind)
    | exact resolve eq1283 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq2449
  have eq3401 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) = X1 ∨ (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3343 X0 X1
       have i₂ := eq61 X1 X1 X1
       grind)
    | (have i₁ := eq3343 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq61 eq3343
    | (have j0 := eq3343 X0 X1
       grind)
    | exact resolve eq3343 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3402 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3401
  have eq3403 : ∀ X0 X1 : G, (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) = X1 ∨ (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3342 X0 X1
       have i₂ := eq61 X1 X1 X1
       grind)
    | (have i₁ := eq3342 X0 X1
       have i₂ := eq61 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq61 eq3342
    | (have j0 := eq3342 X0 X1
       grind)
    | exact resolve eq3342 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3404 : ∀ X0 X1 : G, (M.op (τ (M.op X0 (σ X1))) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3403 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq3447 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X1 (σ (τ X0)))) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3404 X1 (τ X0)
       have i₂ := eq393 X0
       grind)
    | exact superpose eq393 eq3404
    | exact resolve eq3404 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq3404
  have eq3476 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X1 X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3447 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3447
    | exact resolve eq3447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447
  have eq3681 : ∀ X0 X1 X2 : G, (τ (M.op X2 X0)) = (M.op (M.op X1 (τ (M.op X2 X0))) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (τ (M.op X2 X0)) (τ (M.op X0 X0))
       have i₂ := eq3476 X0 X2
       grind)
    | exact superpose eq3476 eq61
    | exact resolve eq61 eq3476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq3476
  have eq4042 : ∀ X0 X1 X2 : G, (M.op (τ (τ (M.op X1 (σ (σ X0))))) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (τ (τ (M.op X0 (σ (σ X1))))) (M.op X1 X1) x
       have i₂ := eq3402 X0 X1
       grind)
    | exact superpose eq3402 eq62
    | exact resolve eq62 eq3402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq3402
  have eq4583 : ∀ X0 X2 X3 : G, (τ X0) = (M.op (M.op X3 (τ X0)) (τ (M.op X0 X2))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3681 (M.op X0 X2) x (τ (τ (M.op x (σ (σ X0)))))
       have i₂ := eq4042 X0 x X2
       grind)
    | exact superpose eq4042 eq3681
    | exact resolve eq3681 eq4042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4042
  have eq4790 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3681 X1 (M.op x (τ X0)) X0
       have i₂ := eq4583 X0 X1 x
       grind)
    | exact superpose eq4583 eq3681
    | exact resolve eq3681 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3681 eq4583
  have eq4876 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4790 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4790
    | exact resolve eq4790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4790
  have eq5162 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq4876 X0 X1
       grind)
    | exact superpose eq4876 eq11
    | exact resolve eq11 eq4876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4876
  have eq5442 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5162 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5162
    | exact resolve eq5162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5162
  have eq5834 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5442 y x
       grind)
    | exact superpose eq5442 eq16
    | (have r₁ := eq16
       have r₂ := eq5442 y x
       grind)
    | exact resolve eq16 eq5442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5442
  have eq5945 : False := by grind
  exact eq5945

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq353 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq353 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq353 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq353 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq365 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq354 (σ X0)
       grind)
    | exact superpose eq354 eq15
    | exact resolve eq15 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq354 (τ X0)
       grind)
    | exact superpose eq354 eq31
    | exact resolve eq31 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq378 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq371
    | exact resolve eq371 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq384 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365 X0
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq365
    | exact resolve eq365 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq365
  have eq677 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq702 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X1
       have i₂ := eq384 X1
       grind)
    | exact superpose eq384 eq677
    | (have j0 := eq677 X0 X1
       grind)
    | exact resolve eq677 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq716 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq702
    | (have j0 := eq702 X0 X1
       grind)
    | exact resolve eq702 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq3002 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq716
    | (have j0 := eq716 (τ X0) X1
       grind)
    | exact resolve eq716 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq3071 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3002 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3002
    | (have j0 := eq3002 X0 X1
       grind)
    | exact resolve eq3002 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3002
  have eq3095 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3071 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq3071 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq3071 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3071
  have eq3099 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3095 X0 X1
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq3095
    | (have j0 := eq3095 X0 X1
       grind)
    | exact resolve eq3095 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq3101 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3099 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3099
    | (have j0 := eq3099 X0 X1
       grind)
    | exact resolve eq3099 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3099
  have eq3103 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3101 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3101
    | (have j0 := eq3101 X1 (τ X0)
       grind)
    | exact resolve eq3101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3101 (σ X1) X0
       grind)
    | exact superpose eq3101 eq15
    | (have j1 := eq3101 (σ X1) X0
       grind)
    | exact resolve eq15 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq3173 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3123 X0 X1
       have i₂ := eq384 X1
       grind)
    | exact superpose eq384 eq3123
    | (have j0 := eq3123 X0 X1
       grind)
    | exact resolve eq3123 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123
  have eq3191 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3103 X0 X1
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq3103
    | (have j0 := eq3103 X0 X1
       grind)
    | exact resolve eq3103 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3103
  have eq3199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3191 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3191
    | (have j0 := eq3191 X0 X1
       grind)
    | exact resolve eq3191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq3235 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq3199 (τ X0) X1
       grind)
    | exact superpose eq3199 eq17
    | (have j1 := eq3199 X1 (τ X0)
       grind)
    | exact resolve eq17 eq3199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3199
  have eq3290 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3235 X0 X1
       have i₂ := eq378 X0
       grind)
    | exact superpose eq378 eq3235
    | (have j0 := eq3235 X0 X1
       grind)
    | exact resolve eq3235 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq3235
  have eq3648 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3290 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3290
    | (have j0 := eq3290 (σ X0) X1
       grind)
    | exact resolve eq3290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq3720 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3648 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3648
    | (have j0 := eq3648 X0 X1
       grind)
    | exact resolve eq3648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3648
  have eq3727 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3720 X0 X1
       have i₂ := eq384 X0
       grind)
    | exact superpose eq384 eq3720
    | (have j0 := eq3720 X0 X1
       grind)
    | exact resolve eq3720 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3730 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3727 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3727
    | (have j0 := eq3727 X0 X1
       grind)
    | exact resolve eq3727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727
  have eq4277 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3173 x y
       grind)
    | exact superpose eq3173 eq16
    | (have j1 := eq3173 x y
       grind)
    | exact resolve eq16 eq3173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq4364 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq4277
       have i₂ := eq3730 x y
       grind)
    | exact superpose eq3730 eq4277
    | (have j1 := eq3730 x y
       grind)
    | (have r₁ := eq4277
       have r₂ := eq3730 x y
       grind)
    | exact resolve eq4277 eq3730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730 eq4277
  have eq4365 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4364
  have eq4395 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y y
       have i₂ := eq4365
       grind)
    | exact superpose eq4365 eq61
    | exact resolve eq61 eq4365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4396 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq4365
       grind)
    | exact superpose eq4365 eq61
    | exact resolve eq61 eq4365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq4414 : (M.op x x) = (M.op y x) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67 x (M.op x y) x
       have i₂ := eq4395 x
       grind)
    | exact superpose eq4395 eq67
    | exact resolve eq67 eq4395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4395
  have eq4446 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4396 x
       have i₂ := eq4414
       grind)
    | exact superpose eq4414 eq4396
    | exact resolve eq4396 eq4414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396 eq4414
  have eq4465 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq4446
  have eq4466 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4465
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq4465
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq4465
    | exact resolve eq4465 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4465
  have eq4467 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4466
       grind)
    | exact superpose eq4466 eq16
    | exact resolve eq16 eq4466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq4468 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq4467
       have r₂ := eq384 x
       grind)
    | exact resolve eq4467 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467
  have eq4497 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq384 (M.op y y)
       have i₂ := eq4468
       grind)
    | exact superpose eq4468 eq384
    | exact resolve eq384 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468
  have eq4536 : (σ (M.op (M.op y y) (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq4497
       have i₂ := eq384 (M.op x x)
       grind)
    | exact superpose eq384 eq4497
    | exact resolve eq4497 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq4554 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq4536
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq4536
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq4536
    | exact resolve eq4536 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4536
  have eq4555 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4554
       have i₂ := eq61 y y y
       grind)
    | (have i₁ := eq4554
       have i₂ := eq61 x (M.op (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq61 eq4554
    | exact resolve eq4554 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq4554
  have eq4556 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4555
       grind)
    | exact superpose eq4555 eq16
    | exact resolve eq16 eq4555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4557 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4555
       grind)
    | exact superpose eq4555 eq10
    | exact resolve eq10 eq4555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4555
  have eq4630 : x = y := by
    first
    | (have i₁ := eq4557
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4557
    | exact resolve eq4557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq4631 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4556
       have i₂ := eq384 x
       grind)
    | exact superpose eq384 eq4556
    | exact resolve eq4556 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq4556
  have eq4632 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4631
       have i₂ := eq4630
       grind)
    | exact superpose eq4630 eq4631
    | exact resolve eq4631 eq4630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4630 eq4631
  have eq4633 : False := by grind
  exact eq4633

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pyy_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq116 sF1
       grind)
    | exact superpose eq116 eq139
    | exact resolve eq139 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq143 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq116 sF0
       grind)
    | exact superpose eq116 eq140
    | exact resolve eq140 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq140
  have eq165 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq143 eq16
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq259 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
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
  have eq260 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq52 X0 X0 x
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq52
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
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
  have eq343 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = X2 ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 X2
       have i₂ := eq11 X2 X0
       grind)
    | (have i₁ := eq52 X0 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq52
    | (have j1 := eq11 X2 X0
       grind)
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
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
  have eq355 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq376 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq339 eq50
    | exact resolve eq50 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq414 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k y (M.op (M.op x y) (M.op x y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq376 eq13
    | (have j0 := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq13 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq421 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq50 eq414
    | exact resolve eq414 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq414
  have eq9771 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 X1 X1
       have i₂ := eq343 X1 X0 X0
       grind)
    | exact superpose eq343 eq330
    | (have j0 := eq330 X0 X1 x
       have j1 := eq343 X1 X1 X0
       grind)
    | exact resolve eq330 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq343
  have eq9851 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9771 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9771
  have eq21312 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq9851 y x
       grind)
    | exact superpose eq9851 eq75
    | (have j1 := eq9851 y x
       grind)
    | exact resolve eq75 eq9851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21501 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21312
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21312
    | exact resolve eq21312 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21312
  have eq21523 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq21501
    | exact resolve eq21501 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21501
  have eq21536 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq21523
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21523
    | exact resolve eq21523 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21523
  have eq21557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21536 eq9851
    | (have j0 := eq9851 (σ y) (σ x)
       grind)
    | exact resolve eq9851 eq21536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq21557
    | exact resolve eq21557 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21557
  have eq21588 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq21568
       have r₂ := eq27
       grind)
    | exact resolve eq21568 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21568
  have eq21600 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq21588
    | exact resolve eq21588 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21588
  have eq21605 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21600 eq27
    | exact resolve eq27 eq21600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21607 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21600 eq67
    | (have r₁ := eq67
       have r₂ := eq21600
       grind)
    | exact resolve eq67 eq21600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq21608 : (σ x) = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21600 eq260
    | exact resolve eq260 eq21600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq21639 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21607
  have eq21901 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21608 eq355
    | exact resolve eq355 eq21608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq21608
  have eq21933 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21600 eq21901
    | exact resolve eq21901 eq21600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21600 eq21901
  have eq21966 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21933
  have eq22848 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21639 eq21536
    | exact resolve eq21536 eq21639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21536 eq21639
  have eq22856 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq22848
  have eq23004 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22856 eq21966
    | exact resolve eq21966 eq22856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21966 eq22856
  have eq23097 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq23004
  have eq23107 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq23097
       have r₂ := eq21605
       grind)
    | exact resolve eq23097 eq21605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21605 eq23097
  have eq23127 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23107 eq29
    | exact resolve eq29 eq23107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23107
  have eq23255 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq23127
    | exact resolve eq23127 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23127
  have eq23256 : x = (M.op x y) ∨ x = y := by grind
  clear eq23255
  have eq23276 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq23256 eq20
    | exact resolve eq20 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23327 : x = (M.op (M.op x x) x) ∨ x = y := by
    first
    | exact superpose eq23256 eq259
    | exact resolve eq259 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq23429 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq23276
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23276
    | exact resolve eq23276 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23276
  have eq23721 : x = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq353 (M.op x x)
       have i₂ := eq23327
       grind)
    | exact superpose eq23327 eq353
    | exact resolve eq353 eq23327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq23327
  have eq23852 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq23256 eq23721
    | exact resolve eq23721 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23721
  have eq23886 : x = (M.op x x) ∨ x = y := by grind
  clear eq23852
  have eq23889 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq124
       have i₂ := eq23886
       grind)
    | exact superpose eq23886 eq124
    | exact resolve eq124 eq23886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq23886
  have eq24009 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq23889
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23889
    | exact resolve eq23889 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23889
  have eq24014 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq23429 eq24009
    | exact resolve eq24009 eq23429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24009
  have eq24130 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq24014
  have eq24196 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq24130 eq165
    | exact resolve eq165 eq24130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq24130
  have eq24307 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq24196
    | exact resolve eq24196 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq24196
  have eq24364 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq24307 eq421
    | (have r₁ := eq421
       have r₂ := eq24307
       grind)
    | exact resolve eq421 eq24307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq24307
  have eq24469 : (M.op x y) = (k y (M.op x y)) ∨ x = y := by grind
  clear eq24364
  have eq24768 : x = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq23256 eq24469
    | exact resolve eq24469 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23256 eq24469
  have eq24803 : x = (k y x) ∨ x = y := by grind
  clear eq24768
  have eq24823 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq24803
       grind)
    | exact superpose eq24803 eq75
    | exact resolve eq75 eq24803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq24803
  have eq24866 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq24823
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24823
    | exact resolve eq24823 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24823
  have eq24939 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24866 eq9851
    | (have j0 := eq9851 (σ y) (σ x)
       grind)
    | exact resolve eq9851 eq24866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9851 eq24866
  have eq24949 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24939
  have eq24967 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq24949
    | exact resolve eq24949 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24949
  have eq24986 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24967 eq27
    | exact resolve eq27 eq24967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24967
  have eq25029 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq24986
       have r₂ := eq23429
       grind)
    | exact resolve eq24986 eq23429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23429 eq24986
  have eq25031 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq25029 eq29
    | exact resolve eq29 eq25029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25029
  have eq25165 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq25031
    | exact resolve eq25031 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25031
  have eq25166 : x = y := by grind
  clear eq25165
  have eq25185 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25166
       grind)
    | exact superpose eq25166 eq18
    | exact resolve eq18 eq25166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25186 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq25166
       grind)
    | exact superpose eq25166 eq24
    | exact resolve eq24 eq25166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25166
  have eq25311 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25186
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25186
    | exact resolve eq25186 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25186
  have eq25551 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25311 eq26
    | exact resolve eq26 eq25311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq25311
  have eq25858 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq25551 eq122
    | exact resolve eq122 eq25551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq25551
  have eq25983 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq25858
       have i₂ := eq25185
       grind)
    | exact superpose eq25185 eq25858
    | exact resolve eq25858 eq25185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25185 eq25858
  have eq26434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25983 eq15
    | exact resolve eq15 eq25983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25983
  have eq26514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq26434
    | exact resolve eq26434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq26434
  have eq26533 : False := by grind
  exact eq26533
