import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq66 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
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
  clear eq36
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
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
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq76
    | exact resolve eq76 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq119 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq116
    | exact resolve eq116 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
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
  have eq128 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq102
    | exact resolve eq102 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq128
    | exact resolve eq128 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq128
  have eq254 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
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
  have eq255 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq254 eq14
    | exact resolve eq14 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq267 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq267 eq14
    | exact resolve eq14 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq566 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
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
  have eq575 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
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
  have eq577 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq578 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq55
  have eq629 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op (M.op (M.op x y) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq631 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq832 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
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
  clear eq56
  have eq1967 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq577 eq566
    | exact resolve eq566 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq1971 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq578 eq566
    | exact resolve eq566 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq578
  have eq2195 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq575 X1 X0
       grind)
    | exact superpose eq575 eq14
    | exact resolve eq14 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq2275 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2195 X1 (M.op X0 X0)
       have i₂ := eq2195 X0 X0
       grind)
    | exact superpose eq2195 eq2195
    | exact resolve eq2195 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2286 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq2195 X1 X0
       grind)
    | exact superpose eq2195 eq14
    | exact resolve eq14 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2723 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq629 (M.op sF0 X0) X0
       have i₂ := eq14 X0 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq14 eq629
    | exact resolve eq629 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq2823 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq631 (M.op sF4 X0) X0
       have i₂ := eq14 X0 sF4 (M.op sF4 X0)
       grind)
    | exact superpose eq14 eq631
    | exact resolve eq631 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq6586 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq255 eq2723
    | exact resolve eq2723 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq2723
  have eq6654 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq6586
       have i₂ := eq2195 x x
       grind)
    | exact superpose eq2195 eq6586
    | exact resolve eq6586 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6586
  have eq7211 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq268 eq2823
    | exact resolve eq2823 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq2823
  have eq7282 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq7211
       have i₂ := eq2195 sF2 sF2
       grind)
    | exact superpose eq2195 eq7211
    | exact resolve eq7211 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7211
  have eq7620 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq832 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq832
    | exact resolve eq832 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq832
  have eq7740 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7620 X0 X1
       have i₂ := eq2195 X0 X0
       grind)
    | exact superpose eq2195 eq7620
    | exact resolve eq7620 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7620
  have eq7852 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq7282 eq7740
    | exact resolve eq7740 eq7282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7740
  have eq8078 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq7852 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq7852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7852
  have eq8110 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq8078
       have i₂ := eq2195 sF4 sF4
       grind)
    | exact superpose eq2195 eq8078
    | exact resolve eq8078 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8078
  have eq57394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq57394
    | exact resolve eq57394 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57394
  have eq57411 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq57406
       have r₂ := eq27
       grind)
    | exact resolve eq57406 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57406
  have eq57413 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq57411
    | exact resolve eq57411 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57411
  have eq57415 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq57413
    | exact resolve eq57413 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57413
  have eq57418 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57415 eq7282
    | exact resolve eq7282 eq57415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7282
  have eq57419 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57415 eq110
    | (have r₁ := eq110
       have r₂ := eq57415
       grind)
    | exact resolve eq110 eq57415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq57415
  have eq57564 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq57419
  have eq57565 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq57564
  have eq57568 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57418 eq272
    | exact resolve eq272 eq57418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq57418
  have eq60721 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57565 eq97
    | exact resolve eq97 eq57565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57565
  have eq60737 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60721
  have eq60742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60737 eq57568
    | exact resolve eq57568 eq60737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57568 eq60737
  have eq60863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq60742
  have eq60866 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq60863
       have r₂ := eq27
       grind)
    | exact resolve eq60863 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60863
  have eq60869 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq60866
       grind)
    | exact superpose eq60866 eq109
    | (have r₁ := eq109
       have r₂ := eq60866
       grind)
    | exact resolve eq109 eq60866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60870 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq60866
       grind)
    | exact superpose eq60866 eq120
    | exact resolve eq120 eq60866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60875 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6654
       have i₂ := eq60866
       grind)
    | exact superpose eq60866 eq6654
    | exact resolve eq6654 eq60866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60866
  have eq61022 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60869
  have eq61023 : (k y x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq61022
  have eq61033 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq60870
    | exact resolve eq60870 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60870
  have eq61192 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60875 eq259
    | exact resolve eq259 eq60875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60875
  have eq63696 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq61023
       grind)
    | exact superpose eq61023 eq75
    | exact resolve eq75 eq61023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61023
  have eq71988 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63696
       have i₂ := eq61192
       grind)
    | exact superpose eq61192 eq63696
    | exact resolve eq63696 eq61192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61192 eq63696
  have eq72050 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq71988
  have eq72057 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq72050
    | exact resolve eq72050 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72050
  have eq72273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72057 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq72057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72057
  have eq72287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq72273
    | exact resolve eq72273 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72273
  have eq72292 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq72287
       have r₂ := eq27
       grind)
    | exact resolve eq72287 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72287
  have eq72294 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq72292
    | exact resolve eq72292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72292
  have eq72296 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq72294
    | exact resolve eq72294 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72294
  have eq72297 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq72296
  have eq72456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72297 eq61033
    | exact resolve eq61033 eq72297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61033 eq72297
  have eq72620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq72456
  have eq72625 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq72620
       have r₂ := eq27
       grind)
    | exact resolve eq72620 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72620
  have eq72627 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72625 eq27
    | exact resolve eq27 eq72625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72630 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72625 eq67
    | (have r₁ := eq67
       have r₂ := eq72625
       grind)
    | exact resolve eq67 eq72625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq72683 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72625 eq1971
    | exact resolve eq1971 eq72625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq72717 : (σ x) ≠ (σ x) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72625 eq8110
    | (have r₁ := eq8110
       have r₂ := eq72625
       grind)
    | exact resolve eq8110 eq72625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8110
  have eq72737 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq72717
  have eq72739 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq72630
  have eq72750 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq72683
    | exact resolve eq72683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72683
  have eq72758 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72625 eq72750
    | exact resolve eq72750 eq72625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72625 eq72750
  have eq72895 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq72758
  have eq73205 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72895 eq2195
    | exact resolve eq2195 eq72895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73384 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73205 eq129
    | exact resolve eq129 eq73205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73205
  have eq73523 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq73384
    | exact resolve eq73384 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq73384
  have eq77634 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72895 eq72737
    | exact resolve eq72737 eq72895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72737 eq72895
  have eq77658 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq77634
  have eq77666 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77658 eq97
    | exact resolve eq97 eq77658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq77658
  have eq77686 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq77666
  have eq77693 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq77686
       have r₂ := eq72627
       grind)
    | exact resolve eq77686 eq72627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72627 eq77686
  have eq77702 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq77693
       grind)
    | exact superpose eq77693 eq109
    | (have r₁ := eq109
       have r₂ := eq77693
       grind)
    | exact resolve eq109 eq77693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq77710 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6654
       have i₂ := eq77693
       grind)
    | exact superpose eq77693 eq6654
    | exact resolve eq6654 eq77693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6654 eq77693
  have eq77876 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y x) := by grind
  clear eq77702
  have eq77877 : x = (M.op x y) ∨ (k y x) = (M.op y x) := by grind
  clear eq77876
  have eq78505 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77710 eq259
    | exact resolve eq259 eq77710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq77710
  have eq83410 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72739 eq93
    | exact resolve eq93 eq72739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq72739
  have eq83436 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq83410
    | exact resolve eq83410 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq83410
  have eq83438 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq83436
       have r₂ := eq66
       grind)
    | exact resolve eq83436 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq83436
  have eq83443 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq83438
       grind)
    | exact superpose eq83438 eq75
    | exact resolve eq75 eq83438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83485 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq83443
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq83443
    | exact resolve eq83443 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83443
  have eq99645 : (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77877
       have i₂ := eq83438
       grind)
    | exact superpose eq83438 eq77877
    | exact resolve eq77877 eq83438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77877 eq83438
  have eq104795 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73523
       have i₂ := eq99645
       grind)
    | exact superpose eq99645 eq73523
    | exact resolve eq73523 eq99645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73523 eq99645
  have eq104937 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq104795
  have eq104957 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78505
       have i₂ := eq104937
       grind)
    | exact superpose eq104937 eq78505
    | exact resolve eq78505 eq104937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78505 eq104937
  have eq105100 : x = (M.op x y) := by grind
  clear eq104957
  have eq105124 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq105100 eq20
    | exact resolve eq20 eq105100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq105131 : (σ (k y x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq105100 eq77
    | exact resolve eq77 eq105100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq105240 : y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq105100 eq1967
    | exact resolve eq1967 eq105100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq105316 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq105240
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105240
    | exact resolve eq105240 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq105240
  have eq105380 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq105131
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq105131
    | exact resolve eq105131 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq105131
  have eq105384 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq105124
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105124
    | exact resolve eq105124 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105124
  have eq105393 : y = (M.op x x) := by
    first
    | exact superpose eq105100 eq105316
    | exact resolve eq105316 eq105100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105100 eq105316
  have eq105424 : (M.op (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq83485 eq105380
    | exact resolve eq105380 eq83485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83485 eq105380
  have eq105431 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq105384 eq26
    | exact resolve eq26 eq105384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105623 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq105393
       grind)
    | exact superpose eq105393 eq120
    | exact resolve eq120 eq105393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq105794 : x = (M.op y y) := by
    first
    | (have i₁ := eq2195 x x
       have i₂ := eq105393
       grind)
    | exact superpose eq105393 eq2195
    | exact resolve eq2195 eq105393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195 eq105393
  have eq105848 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq105384 eq105623
    | exact resolve eq105623 eq105384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105623
  have eq105876 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq105848
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq105848
    | exact resolve eq105848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq105848
  have eq106022 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq105794
       grind)
    | exact superpose eq105794 eq119
    | exact resolve eq119 eq105794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq105794
  have eq106208 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq106022
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq106022
    | exact resolve eq106022 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq106022
  have eq106228 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq105384 eq106208
    | exact resolve eq106208 eq105384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105384 eq106208
  have eq106265 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq105876 eq2275
    | exact resolve eq2275 eq105876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq106266 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq105876 eq2286
    | exact resolve eq2286 eq105876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq110523 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq106228 eq105424
    | exact resolve eq105424 eq106228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105424 eq106228
  have eq110529 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq110523 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq110523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110543 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq110529
  have eq110554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq105431 eq110543
    | exact resolve eq110543 eq105431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110543
  have eq110561 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq110554
       have r₂ := eq27
       grind)
    | exact resolve eq110554 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110554
  have eq110566 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq105431 eq110561
    | exact resolve eq110561 eq105431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105431 eq110561
  have eq110571 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105876 eq110566
    | exact resolve eq110566 eq105876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110566
  have eq110577 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq110571 eq27
    | exact resolve eq27 eq110571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq115213 : ∀ X0 : G, (σ y) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (M.op X0 (σ y)) (σ (M.op x y))) = (k (M.op X0 (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq106266 eq12
    | (have j0 := eq12 (M.op X0 (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq12 eq106266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106266
  have eq115343 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (M.op (M.op X0 (σ y)) (σ (M.op x y))) = (k (M.op X0 (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq115213 X0
       grind)
    | (have r₁ := eq115213 X0
       have r₂ := eq105876
       grind)
    | exact resolve eq115213 eq105876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105876 eq115213
  have eq115353 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ (M.op x y))) = (k (M.op X0 (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq115343 X0
       grind)
    | (have r₁ := eq115343 X0
       have r₂ := eq110577
       grind)
    | exact resolve eq115343 eq110577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115343
  have eq115355 : ∀ X0 : G, (σ y) = (k (M.op X0 (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq106265 eq115353
    | exact resolve eq115353 eq106265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106265 eq115353
  have eq119008 : (σ y) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq115355
    | (have j0 := eq115355 (σ x)
       grind)
    | exact resolve eq115355 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq115355
  have eq119043 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq110571 eq119008
    | exact resolve eq119008 eq110571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110571 eq119008
  have eq119068 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq110523 eq119043
    | exact resolve eq119043 eq110523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110523 eq119043
  have eq119085 : False := by grind
  exact eq119085

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 X0 y
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
  have eq50 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y x X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31
    | (have j0 := eq31 x
       grind)
    | exact resolve eq31 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq90 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ y)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq173 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134
    | exact resolve eq134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq200 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq304 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X1 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq322 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq342 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 X0 (τ X0)
       have i₂ := eq100 (τ X0)
       grind)
    | exact superpose eq100 eq50
    | (have j1 := eq100 (τ X0)
       grind)
    | exact resolve eq50 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq173 X0 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq173
    | (have j1 := eq100 X0
       grind)
    | exact resolve eq173 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq100 sF2
       grind)
    | exact superpose eq100 eq61
    | (have j1 := eq100 (σ x)
       grind)
    | exact resolve eq61 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq100 sF3
       grind)
    | exact superpose eq100 eq72
    | (have j1 := eq100 (σ y)
       grind)
    | exact resolve eq72 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq348 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq342
    | (have j0 := eq342 X0
       grind)
    | exact resolve eq342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq553 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X3) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq55 X1 X0 x
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq55 x X0 x
       grind)
    | exact superpose eq55 eq90
    | exact resolve eq90 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq626 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq57 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op y X1) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq560 eq55
    | exact resolve eq55 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq760 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq93 eq553
    | exact resolve eq553 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq553
  have eq891 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq626 X1 X0
       grind)
    | exact superpose eq626 eq9
    | exact resolve eq9 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq945 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq891 X1 (M.op X0 X0)
       have i₂ := eq891 X0 X0
       grind)
    | exact superpose eq891 eq891
    | exact resolve eq891 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq1120 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq322 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq322
    | (have j0 := eq322 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq322 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq1760 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq945 X0 X1
       grind)
    | exact superpose eq945 eq9
    | exact resolve eq9 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1767 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq56 (M.op y y)
       have i₂ := eq945 y x
       grind)
    | exact superpose eq945 eq56
    | exact resolve eq56 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1776 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq58 (M.op sF3 sF3)
       have i₂ := eq945 sF3 sF2
       grind)
    | exact superpose eq945 eq58
    | exact resolve eq58 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1781 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq95 x (M.op sF4 sF4)
       have i₂ := eq945 sF4 (M.op (M.op sF2 x) sF3)
       grind)
    | exact superpose eq945 eq95
    | exact resolve eq95 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq945
  have eq1957 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X0 X0) X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X1 X0) (M.op X0 X0) X2
       have i₂ := eq1760 X0 X1
       grind)
    | exact superpose eq1760 eq55
    | exact resolve eq55 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2073 : ∀ X0 : G, (k (τ X0) (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq173 X0 (M.op X0 X0)
       have i₂ := eq954 X0
       grind)
    | exact superpose eq954 eq173
    | exact resolve eq173 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq5488 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq346
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq346
    | (have j1 := eq100 (σ x)
       grind)
    | exact resolve eq346 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq7279 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y x) (M.op x y)) := by
    first
    | exact superpose eq695 eq55
    | exact resolve eq55 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq695
  have eq11922 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 (M.op (M.op X0 X0) X1) x X0
       have i₂ := eq1957 X0 (M.op (M.op (M.op (M.op X0 X0) X1) x) X0) X1
       grind)
    | exact superpose eq1957 eq57
    | exact resolve eq57 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1957
  have eq12222 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11922 (M.op X1 X1) X1
       have i₂ := eq1760 X1 X1
       grind)
    | exact superpose eq1760 eq11922
    | exact resolve eq11922 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760 eq11922
  have eq14457 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq663 (M.op X1 X0) X1 X0
       have i₂ := eq304 X1 (M.op X1 X0) X0
       grind)
    | exact superpose eq304 eq663
    | exact resolve eq663 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq663
  have eq14963 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op (M.op (M.op X1 X0) X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X0
       have i₂ := eq14457 X0 X1
       grind)
    | exact superpose eq14457 eq9
    | exact resolve eq9 eq14457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14457
  have eq20433 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39 eq348
    | exact resolve eq348 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq20465 : (σ (k x x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq61 eq20433
    | exact resolve eq20433 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20433
  have eq100002 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (M.op X0 (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1776 eq14963
    | exact resolve eq14963 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14963
  have eq131014 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1120 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1120
    | (have j0 := eq1120 x y
       grind)
    | exact resolve eq1120 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq131325 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq131014
    | exact resolve eq131014 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131014
  have eq131783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq131325
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq131325
    | exact resolve eq131325 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131325
  have eq132167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq131783
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq131783
    | exact resolve eq131783 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131783
  have eq132460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq132167
    | exact resolve eq132167 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132167
  have eq132710 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq132460
       have r₂ := eq28
       grind)
    | exact resolve eq132460 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132460
  have eq132875 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132710
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq132710
    | exact resolve eq132710 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132710
  have eq132976 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132875
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq132875
    | exact resolve eq132875 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132875
  have eq133038 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132976
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq132976
    | exact resolve eq132976 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132976
  have eq133087 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq133038
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq133038
    | exact resolve eq133038 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133038
  have eq133260 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq133087 eq12222
    | exact resolve eq12222 eq133087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133087
  have eq133280 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq133260
       have i₂ := eq891 sF2 sF2
       grind)
    | exact superpose eq891 eq133260
    | exact resolve eq133260 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133260
  have eq133385 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq133280
  have eq133500 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq62 eq133385
    | exact resolve eq133385 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133385
  have eq133514 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq133500
    | exact resolve eq133500 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133500
  have eq156268 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq133514
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq133514
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq133514 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133514
  have eq156299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq156268
  have eq156310 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq156299
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq156299
    | exact resolve eq156299 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156299
  have eq156316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq156310
    | exact resolve eq156310 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156310
  have eq156320 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq156316
       have r₂ := eq28
       grind)
    | exact resolve eq156316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156316
  have eq156498 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12222 y y
       have i₂ := eq156320
       grind)
    | exact superpose eq156320 eq12222
    | exact resolve eq12222 eq156320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156320
  have eq156539 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq156498
       have i₂ := eq891 x x
       grind)
    | exact superpose eq891 eq156498
    | exact resolve eq156498 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq156498
  have eq156666 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq156755 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12222 x x
       have i₂ := eq156539
       grind)
    | exact superpose eq156539 eq12222
    | exact resolve eq12222 eq156539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12222 eq156539
  have eq156800 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq156666
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq156666
    | exact resolve eq156666 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156666
  have eq157129 : (τ x) = (k (τ y) (τ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq343 y
       have i₂ := eq156755
       grind)
    | exact superpose eq156755 eq343
    | exact resolve eq343 eq156755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq156755
  have eq157232 : (τ x) = (k (τ y) (τ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq157129
  have eq164967 : (σ (τ x)) = (k y (σ (τ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50 y (τ y)
       have i₂ := eq157232
       grind)
    | exact superpose eq157232 eq50
    | exact resolve eq50 eq157232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq157232
  have eq164972 : (k y y) = (σ (τ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq164967
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq164967
    | exact resolve eq164967 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164967
  have eq164980 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq164972
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq164972
    | exact resolve eq164972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164972
  have eq164992 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq347
       have i₂ := eq164980
       grind)
    | exact superpose eq164980 eq347
    | exact resolve eq347 eq164980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq165012 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq164992
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq164992
    | exact resolve eq164992 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164992
  have eq184043 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq165012 eq100002
    | exact resolve eq100002 eq165012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100002
  have eq184175 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1776 eq184043
    | exact resolve eq184043 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776 eq184043
  have eq185796 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq165012 eq184175
    | exact resolve eq184175 eq165012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184175
  have eq185981 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq185796
  have eq186070 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq185981 eq954
    | exact resolve eq954 eq185981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185981
  have eq186180 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62 eq186070
    | exact resolve eq186070 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq186070
  have eq186189 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq186180
    | exact resolve eq186180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186180
  have eq186982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq186189
       have i₂ := eq156800
       grind)
    | exact superpose eq156800 eq186189
    | exact resolve eq186189 eq156800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186189
  have eq187016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq186982
  have eq187027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq187016
    | exact resolve eq187016 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187016
  have eq187034 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq187027
       have r₂ := eq28
       grind)
    | exact resolve eq187027 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187027
  have eq187038 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq187034 eq28
    | exact resolve eq28 eq187034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187089 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq187034 eq760
    | exact resolve eq760 eq187034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq187117 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq187034 eq1781
    | exact resolve eq1781 eq187034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781 eq187034
  have eq187454 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) (τ (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq187089 eq200
    | exact resolve eq200 eq187089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq187089
  have eq187566 : y = (k (τ (M.op (σ y) (σ y))) y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40 eq187454
    | exact resolve eq187454 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187454
  have eq187591 : (τ (σ y)) = (k (τ (σ y)) (τ (M.op (σ y) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq187117 eq2073
    | exact resolve eq2073 eq187117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073 eq187117
  have eq187772 : y = (k y (τ (M.op (σ y) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40 eq187591
    | exact resolve eq187591 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187591
  have eq195469 : y = (k (τ (σ y)) y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq165012 eq187566
    | exact resolve eq187566 eq165012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165012 eq187566
  have eq195496 : y = (k (τ (σ y)) y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq195469
  have eq195517 : y = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq40 eq195496
    | exact resolve eq195496 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195496
  have eq217596 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq164980
       have i₂ := eq195517
       grind)
    | exact superpose eq195517 eq164980
    | exact resolve eq164980 eq195517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164980 eq195517
  have eq217612 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq217596
  have eq217655 : y = (k y (τ (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq217612 eq187772
    | exact resolve eq187772 eq217612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187772 eq217612
  have eq217860 : y = (k y (τ (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq217655
  have eq217878 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39 eq217860
    | exact resolve eq217860 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217860
  have eq220445 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq156800
       have i₂ := eq217878
       grind)
    | exact superpose eq217878 eq156800
    | exact resolve eq156800 eq217878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156800 eq217878
  have eq220464 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq220445
  have eq220530 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq220464 eq40
    | exact resolve eq40 eq220464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq220464
  have eq220766 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39 eq220530
    | exact resolve eq220530 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220530
  have eq220767 : y = (M.op x y) ∨ x = y := by grind
  clear eq220766
  have eq220771 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq220767 eq21
    | exact resolve eq21 eq220767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221270 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq220771
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq220771
    | exact resolve eq220771 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220771
  have eq221549 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq221270 eq187038
    | (have r₁ := eq187038
       have r₂ := eq221270
       grind)
    | exact resolve eq187038 eq221270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187038 eq221270
  have eq221682 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq221549
  have eq221683 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq221682
  have eq221714 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq221683 eq39
    | exact resolve eq39 eq221683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq221683
  have eq221979 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq221714
    | exact resolve eq221714 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq221714
  have eq222362 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq221979 eq220767
    | exact resolve eq220767 eq221979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220767 eq221979
  have eq222363 : x = y := by grind
  clear eq222362
  have eq222415 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq222363
       grind)
    | exact superpose eq222363 eq19
    | exact resolve eq19 eq222363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq222416 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq222363
       grind)
    | exact superpose eq222363 eq25
    | exact resolve eq25 eq222363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq222547 : x = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq1767
       have i₂ := eq222363
       grind)
    | exact superpose eq222363 eq1767
    | exact resolve eq1767 eq222363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq222979 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq7279
       have i₂ := eq222363
       grind)
    | exact superpose eq222363 eq7279
    | exact resolve eq7279 eq222363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7279 eq222363
  have eq235884 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq222979 eq222547
    | exact resolve eq222547 eq222979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222547 eq222979
  have eq235999 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq222416
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq222416
    | exact resolve eq222416 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222416
  have eq236007 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5488
       have i₂ := eq222415
       grind)
    | exact superpose eq222415 eq5488
    | exact resolve eq5488 eq222415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5488
  have eq236013 : x = (M.op x y) ∨ (σ (k x x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq20465
       have i₂ := eq222415
       grind)
    | exact superpose eq222415 eq20465
    | exact resolve eq20465 eq222415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20465
  have eq239968 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq235999 eq27
    | exact resolve eq27 eq235999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq235999
  have eq249014 : (σ (M.op x y)) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq236013
       have i₂ := eq222415
       grind)
    | exact superpose eq222415 eq236013
    | exact resolve eq236013 eq222415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236013
  have eq249015 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq236007
    | exact resolve eq236007 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236007
  have eq251514 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq239968 eq346
    | exact resolve eq346 eq239968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq253055 : (σ (M.op x y)) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq249014
    | exact resolve eq249014 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249014
  have eq253056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq239968 eq249015
    | exact resolve eq249015 eq239968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249015
  have eq255989 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq239968 eq251514
    | exact resolve eq251514 eq239968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251514
  have eq256005 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq253056
       have r₂ := eq28
       grind)
    | exact resolve eq253056 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253056
  have eq257851 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq239968 eq256005
    | exact resolve eq256005 eq239968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256005
  have eq258612 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq257851
       have i₂ := eq222415
       grind)
    | exact superpose eq222415 eq257851
    | exact resolve eq257851 eq222415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257851
  have eq260160 : (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq954 x
       have i₂ := eq222415
       grind)
    | exact superpose eq222415 eq954
    | exact resolve eq954 eq222415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq222415
  have eq260686 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq261449 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq258612 eq260686
    | exact resolve eq260686 eq258612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258612 eq260686
  have eq261450 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq239968 eq261449
    | exact resolve eq261449 eq239968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239968 eq261449
  have eq261458 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61 eq261450
    | exact resolve eq261450 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq261450
  have eq264526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253055
       have i₂ := eq261458
       grind)
    | exact superpose eq261458 eq253055
    | exact resolve eq253055 eq261458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253055 eq261458
  have eq264549 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq264526
  have eq264564 : x = (M.op x y) := by
    first
    | (have r₁ := eq264549
       have r₂ := eq28
       grind)
    | exact resolve eq264549 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264549
  have eq264575 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq264564 eq21
    | exact resolve eq21 eq264564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq267698 : x = (M.op x x) := by
    first
    | exact superpose eq264564 eq235884
    | exact resolve eq235884 eq264564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235884
  have eq267908 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq264564 eq260160
    | exact resolve eq260160 eq264564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260160 eq264564
  have eq268106 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq255989
       have i₂ := eq267908
       grind)
    | exact superpose eq267908 eq255989
    | exact resolve eq255989 eq267908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255989 eq267908
  have eq269004 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq264575
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq264575
    | exact resolve eq264575 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264575
  have eq269071 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq268106
       have i₂ := eq267698
       grind)
    | exact superpose eq267698 eq268106
    | exact resolve eq268106 eq267698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267698 eq268106
  have eq272329 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq269004 eq23
    | exact resolve eq23 eq269004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq274269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq269004 eq269071
    | exact resolve eq269071 eq269004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269004 eq269071
  have eq277540 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq274269
       have r₂ := eq28
       grind)
    | exact resolve eq274269 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274269
  have eq280056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq277540
       have i₂ := eq272329
       grind)
    | exact superpose eq272329 eq277540
    | exact resolve eq277540 eq272329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272329 eq277540
  have eq281488 : False := by grind
  exact eq281488

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
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
  have eq55 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq56 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq420 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq745 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1652 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq419 eq410
    | exact resolve eq410 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq1656 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq420 eq410
    | exact resolve eq410 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq420
  have eq54193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq54193
    | exact resolve eq54193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54193
  have eq54209 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq54204
       have r₂ := eq28
       grind)
    | exact resolve eq54204 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54204
  have eq54211 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq54209
    | exact resolve eq54209 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54209
  have eq54239 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq54211
  have eq54352 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq54239
    | exact resolve eq54239 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54239
  have eq55184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq54352 eq98
    | exact resolve eq98 eq54352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54352
  have eq55199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55184
  have eq55201 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq55199
       have r₂ := eq28
       grind)
    | exact resolve eq55199 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55199
  have eq55231 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55201
  have eq55344 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55231
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55231
    | exact resolve eq55231 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55231
  have eq56231 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq55344
       grind)
    | exact superpose eq55344 eq73
    | exact resolve eq73 eq55344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55344
  have eq56265 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq56231
    | exact resolve eq56231 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56231
  have eq56946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56265 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq56265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq56946
    | exact resolve eq56946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56946
  have eq56964 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq56959
       have r₂ := eq28
       grind)
    | exact resolve eq56959 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56959
  have eq56966 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq56964
    | exact resolve eq56964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56964
  have eq56967 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq56966
  have eq56996 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq56967
  have eq57109 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq56996
    | exact resolve eq56996 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56996
  have eq57716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57109 eq56265
    | exact resolve eq56265 eq57109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56265 eq57109
  have eq57728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57716
  have eq57732 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq57728
       have r₂ := eq28
       grind)
    | exact resolve eq57728 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57728
  have eq57781 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57732 eq1656
    | exact resolve eq1656 eq57732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656
  have eq57841 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq57781
    | exact resolve eq57781 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57781
  have eq57850 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57732 eq57841
    | exact resolve eq57841 eq57732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57732 eq57841
  have eq57974 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq57850
  have eq58135 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq57974
  have eq58248 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq58135
    | exact resolve eq58135 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58135
  have eq58532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58248 eq98
    | exact resolve eq98 eq58248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq58546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq58532
  have eq58549 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq58546
       have r₂ := eq28
       grind)
    | exact resolve eq58546 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58546
  have eq58580 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq58549
  have eq58693 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58580
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58580
    | exact resolve eq58580 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58580
  have eq59226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq58693
       grind)
    | exact superpose eq58693 eq73
    | exact resolve eq73 eq58693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58693
  have eq59260 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq59226
    | exact resolve eq59226 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59226
  have eq59316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59260 eq58248
    | exact resolve eq58248 eq59260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58248 eq59260
  have eq59328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq59316
  have eq59334 : x = (M.op x y) := by
    first
    | (have r₁ := eq59328
       have r₂ := eq28
       grind)
    | exact resolve eq59328 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59328
  have eq59339 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq59334 eq21
    | exact resolve eq21 eq59334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq59437 : y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59334 eq1652
    | exact resolve eq1652 eq59334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq59497 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq59437
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59437
    | exact resolve eq59437 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59437
  have eq59555 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq59339
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq59339
    | exact resolve eq59339 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59339
  have eq59564 : y = (M.op x x) := by
    first
    | exact superpose eq59334 eq59497
    | exact resolve eq59497 eq59334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59497
  have eq59572 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq59555 eq27
    | exact resolve eq27 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59697 : (M.op x y) = (k y x) := by grind
  clear eq59564
  have eq59819 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq59697
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59697
    | exact resolve eq59697 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq59697
  have eq59842 : x = (k y x) := by
    first
    | exact superpose eq59334 eq59819
    | exact resolve eq59819 eq59334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59334 eq59819
  have eq60142 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq59842
       grind)
    | exact superpose eq59842 eq73
    | exact resolve eq73 eq59842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq60159 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq745 x y
       have i₂ := eq59842
       grind)
    | exact superpose eq59842 eq745
    | (have j0 := eq745 x y
       grind)
    | exact resolve eq745 eq59842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq59842
  have eq60163 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq60159
  have eq60172 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60163
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq60163
    | exact resolve eq60163 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60163
  have eq60186 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq59555 eq60142
    | exact resolve eq60142 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60142
  have eq60189 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60172
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60172
    | exact resolve eq60172 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60172
  have eq60203 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq60186
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60186
    | exact resolve eq60186 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60186
  have eq60206 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq60189
    | exact resolve eq60189 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq60189
  have eq60219 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq59555 eq60203
    | exact resolve eq60203 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60203
  have eq60222 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59555 eq60206
    | exact resolve eq60206 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60206
  have eq60232 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq60222
       have r₂ := eq28
       grind)
    | exact resolve eq60222 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60222
  have eq60242 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60232
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60232
    | exact resolve eq60232 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq60232
  have eq60251 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq59555 eq60242
    | exact resolve eq60242 eq59555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59555 eq60242
  have eq60260 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq60251
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq60251
    | exact resolve eq60251 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq60251
  have eq60324 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq60260
  have eq60446 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq59572 eq60324
    | exact resolve eq60324 eq59572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59572 eq60324
  have eq60447 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60219 eq60446
    | exact resolve eq60446 eq60219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60219 eq60446
  have eq60448 : False := by grind
  exact eq60448

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (k X1 X0) X1
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X2 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq264 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X2 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X1 X0
       have i₂ := eq32 X1 X0 X2
       grind)
    | exact superpose eq32 eq21
    | (have j1 := eq32 X1 X1 X2
       grind)
    | exact resolve eq21 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq32
  have eq389 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq396 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq389 X0 X1
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq389 X0 X0
       have r₂ := eq38 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq389 X0 X1
       have r₂ := eq38 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq389 X0 X1
       have r₂ := eq38 (M.op X1 X0) (k X0 X1)
       grind)
    | exact resolve eq389 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq389
  have eq397 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq396 X0 X1
       have j1 := eq264 X0 X1 X0
       grind)
    | (have r₁ := eq396 X0 X1
       have r₂ := eq264 X0 X1 x
       grind)
    | (have r₁ := eq396 X1 X1
       have r₂ := eq264 X1 X1 x
       grind)
    | (have r₁ := eq396 X1 X1
       have r₂ := eq264 X0 X1 (M.op X1 X1)
       grind)
    | exact resolve eq396 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq396
  have eq1036 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq397
  have eq1053 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1036 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1648 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1053 (σ X1) (σ X0)
       grind)
    | exact superpose eq1053 eq15
    | exact resolve eq15 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1661 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1648 X0 X1
       have i₂ := eq1053 X1 X0
       grind)
    | exact superpose eq1053 eq1648
    | exact resolve eq1648 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq1648
  have eq1673 : False := by grind
  exact eq1673

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq154 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq25 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq173 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq189 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (M.op (σ X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op (σ (M.op x x)) X0) (M.op (σ x) X0) X2
       have i₂ := eq189 x X0
       grind)
    | exact superpose eq189 eq23
    | exact resolve eq23 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq189
  have eq446 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq372 (M.op X1 x) X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq372
    | exact resolve eq372 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq574 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq446 X1 X0
       grind)
    | exact superpose eq446 eq9
    | exact resolve eq9 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq592 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq173
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq173
    | exact resolve eq173 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq593 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq592
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq592
    | exact resolve eq592 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq638 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq593
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq593
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq593 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq593
  have eq639 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq638
  have eq1752 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1 (M.op X0 X0)
       have i₂ := eq24 X0 X0 X1
       grind)
    | exact superpose eq24 eq154
    | exact resolve eq154 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq154
  have eq1804 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1752 X0 X1
       have i₂ := eq574 X0 X0
       grind)
    | exact superpose eq574 eq1752
    | exact resolve eq1752 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq11536 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq639
       grind)
    | exact superpose eq639 eq10
    | exact resolve eq10 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq11579 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq11536
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq11536
    | exact resolve eq11536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11536
  have eq11580 : (M.op y y) = (M.op x x) := by grind
  clear eq11579
  have eq11694 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq1804 y y
       have i₂ := eq11580
       grind)
    | exact superpose eq11580 eq1804
    | exact resolve eq1804 eq11580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804 eq11580
  have eq11704 : x = y := by
    first
    | (have i₁ := eq11694
       have i₂ := eq574 x x
       grind)
    | exact superpose eq574 eq11694
    | exact resolve eq11694 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq11694
  have eq11756 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11704
       grind)
    | exact superpose eq11704 eq16
    | exact resolve eq16 eq11704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11704
  have eq11757 : False := by grind
  exact eq11757

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  clear eq22
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
  have eq75 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
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
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
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
  clear eq72
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq98
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq203 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq363 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (M.op X1 X2) (M.op (M.op (σ x) X0) (σ y))) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
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
  have eq392 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq393 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq398 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq392 eq14
    | exact resolve eq14 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq393 eq14
    | exact resolve eq14 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq448 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) (M.op X0 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 (M.op (M.op X0 X1) X2)) (M.op X0 X1) X2
       have i₂ := eq53 (M.op (M.op X0 X1) X2) X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1487 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq203 eq383
    | exact resolve eq383 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq1794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq107 eq75
    | (have j0 := eq75 (σ y) x
       grind)
    | exact resolve eq75 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1794
    | exact resolve eq1794 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1794
  have eq1798 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1795
       have r₂ := eq27
       grind)
    | exact resolve eq1795 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1841 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1798 eq404
    | exact resolve eq404 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1798 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1798
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1798
       grind)
    | exact resolve eq13 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1865 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1846 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq1868 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1841 eq203
    | exact resolve eq203 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq1892 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1868 eq1487
    | exact resolve eq1487 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868
  have eq1916 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1892 eq1798
    | exact resolve eq1798 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892
  have eq1941 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1916
  have eq1989 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1941
       grind)
    | exact superpose eq1941 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1941
       grind)
    | exact resolve eq13 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2008 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1989 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq2665 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq2008 y
       grind)
    | exact superpose eq2008 eq73
    | exact resolve eq73 eq2008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2008
  have eq4860 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2665
       have i₂ := eq1941
       grind)
    | exact superpose eq1941 eq2665
    | exact resolve eq2665 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941 eq2665
  have eq4885 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4860
  have eq4891 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4885
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4885
    | exact resolve eq4885 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4885
  have eq4895 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4891 eq75
    | (have j0 := eq75 (σ y) x
       grind)
    | exact resolve eq75 eq4891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4891
  have eq4896 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4895
  have eq5042 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4896 eq404
    | exact resolve eq404 eq4896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq5279 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5042 eq203
    | exact resolve eq203 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq5042
  have eq5359 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5279 eq1487
    | exact resolve eq1487 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487 eq5279
  have eq5390 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5359 eq4896
    | exact resolve eq4896 eq5359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896 eq5359
  have eq5416 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5390
  have eq5524 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq5416 eq27
    | exact resolve eq27 eq5416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq5872 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (M.op (M.op (M.op X1 X2) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5416 eq363
    | exact resolve eq363 eq5416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq5416
  have eq6002 : ∀ X3 : G, (M.op (M.op (σ y) X3) (M.op (σ y) X3)) = X3 := by
    intro X3
    first
    | exact superpose eq5872 eq14
    | exact resolve eq14 eq5872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5872
  have eq6126 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq6002 eq53
    | exact resolve eq53 eq6002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq6002
  have eq30122 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) = (M.op (σ y) (M.op X0 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq448 X0 X1 X2
       have i₂ := eq6126 (M.op X0 (M.op (M.op X0 X1) X2))
       grind)
    | exact superpose eq6126 eq448
    | exact resolve eq448 eq6126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq30401 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30122 (M.op X1 x) X1 x
       have i₂ := eq52 X1 X1 x x
       grind)
    | exact superpose eq52 eq30122
    | exact resolve eq30122 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq30122
  have eq76374 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1865 eq85
    | exact resolve eq85 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1865
  have eq283964 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1798 eq76374
    | exact resolve eq76374 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798 eq76374
  have eq284014 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq283964
  have eq284020 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq284014
    | exact resolve eq284014 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq284014
  have eq284048 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75 y y
       have i₂ := eq284020
       grind)
    | exact superpose eq284020 eq75
    | (have j0 := eq75 y x
       grind)
    | exact resolve eq75 eq284020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq284020
  have eq284062 : y = (M.op y y) := by grind
  clear eq284048
  have eq284120 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq398
       have i₂ := eq284062
       grind)
    | exact superpose eq284062 eq398
    | exact resolve eq398 eq284062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq284744 : (M.op (M.op y (M.op x y)) y) = (M.op (σ y) y) := by
    first
    | exact superpose eq284120 eq30401
    | exact resolve eq30401 eq284120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30401 eq284120
  have eq284780 : (M.op y y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq6126 eq284744
    | exact resolve eq284744 eq6126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6126 eq284744
  have eq284851 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq392 eq284780
    | exact resolve eq284780 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq284780
  have eq284876 : y = (M.op x y) := by
    first
    | (have i₁ := eq284851
       have i₂ := eq284062
       grind)
    | exact superpose eq284062 eq284851
    | exact resolve eq284851 eq284062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284062 eq284851
  have eq284882 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq284876 eq20
    | exact resolve eq20 eq284876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq284876
  have eq285329 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq284882
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq284882
    | exact resolve eq284882 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq284882
  have eq285377 : False := by grind
  exact eq285377

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_x_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
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
  have eq63 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq64 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
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
  have eq75 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq107 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X2) X0)) ≠ X0 ∨ (M.op (M.op X1 X2) X0) = (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) ∨ (M.op (M.op X1 X0) (M.op (M.op X1 X2) X0)) = (k (M.op X1 X0) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op (M.op X1 X2) X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 X0) (M.op (M.op X1 X2) X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X2) X0)) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (k (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq148 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq226 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq63 eq14
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq109
    | (have j0 := eq109 (σ X0)
       grind)
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61
    | (have j0 := eq61 x X0 X1 y
       grind)
    | exact resolve eq61 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq61 X1 x x X0
       grind)
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq226 eq62
    | exact resolve eq62 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq521 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq232 eq62
    | exact resolve eq62 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq529 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq63 eq62
    | exact resolve eq62 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq64 eq62
    | exact resolve eq62 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq65 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X0 (σ X0)
       have j1 := eq75 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq761 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq751 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq762 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq761 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq767 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq762
    | (have j0 := eq762 X0 X1
       grind)
    | exact resolve eq762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq768 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq767 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq887 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) X1) (M.op X0 X1)) ≠ X1 ∨ (M.op (M.op (M.op (M.op X0 X2) X1) X3) X1) = (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) X1) (M.op (M.op (M.op (M.op X0 X2) X1) X3) X1)) ∨ (k (M.op X0 X1) (M.op (M.op (M.op (M.op X0 X2) X1) X3) X1)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq108 X0 (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)
       have i₂ := eq65 X0 X1 X2 X3
       grind)
    | exact superpose eq65 eq108
    | (have j0 := eq108 X1 (M.op (M.op (M.op X0 X2) X1) X3) X2
       grind)
    | exact resolve eq108 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq108
  have eq999 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op (M.op x X0) (M.op x y)) y) ∨ y = (M.op y y) ∨ (M.op (M.op (M.op x X0) (M.op x y)) y) = (k (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq63 eq107
    | exact resolve eq107 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1003 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) = (k (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq64 eq107
    | exact resolve eq107 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1520 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq448 (M.op x X0) (M.op (M.op (M.op x x) x) X0)
       have i₂ := eq61 x x x X0
       grind)
    | exact superpose eq61 eq448
    | exact resolve eq448 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq1604 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq451 (M.op x X0) (M.op (M.op (M.op x x) x) X0)
       have i₂ := eq61 x x x X0
       grind)
    | exact superpose eq61 eq451
    | exact resolve eq451 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq1875 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq469
    | exact resolve eq469 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq2139 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq476 X1 X0
       grind)
    | exact superpose eq476 eq14
    | exact resolve eq14 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2245 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq2139 X0 X0
       grind)
    | exact superpose eq2139 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3254 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq517 eq529
    | exact resolve eq529 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq529
  have eq3288 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq3254 X0
       have i₂ := eq476 y (M.op x X0)
       grind)
    | exact superpose eq476 eq3254
    | exact resolve eq3254 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254
  have eq3350 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq521 eq532
    | exact resolve eq532 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq532
  have eq3382 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3350 X0
       have i₂ := eq476 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq476 eq3350
    | exact resolve eq3350 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq3350
  have eq6150 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq3288 eq505
    | exact resolve eq505 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288
  have eq6155 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq3382 eq505
    | exact resolve eq505 eq3382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq7388 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1 (M.op X0 X0)
       have i₂ := eq62 X0 X0 X1
       grind)
    | exact superpose eq62 eq657
    | exact resolve eq657 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7391 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq657 (M.op X1 X0) X1 X0
       have i₂ := eq61 X1 X1 X0 X0
       grind)
    | exact superpose eq61 eq657
    | exact resolve eq657 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq657
  have eq7515 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7388 X0 X1
       have i₂ := eq2139 X0 X0
       grind)
    | exact superpose eq2139 eq7388
    | exact resolve eq7388 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7388
  have eq7644 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq229 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq7515 (M.op x X0) y
       grind)
    | exact superpose eq7515 eq229
    | exact resolve eq229 eq7515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq7646 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq235 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq7515 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq7515 eq235
    | exact resolve eq235 eq7515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq7654 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq505 X1 X0 (M.op X0 X0)
       have i₂ := eq7515 X0 X1
       grind)
    | exact superpose eq7515 eq505
    | exact resolve eq505 eq7515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq7515
  have eq9900 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7644 (M.op x (M.op X0 x))
       have i₂ := eq1875 x X0
       grind)
    | exact superpose eq1875 eq7644
    | exact resolve eq7644 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9987 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7646 (M.op sF2 (M.op x sF2))
       have i₂ := eq1875 sF2 x
       grind)
    | exact superpose eq1875 eq7646
    | exact resolve eq7646 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq11483 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq371 X0
       grind)
    | exact superpose eq371 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq371 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq371 X0
       grind)
    | exact resolve eq13 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq11531 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11483 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq11483 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq11483 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11483
  have eq11726 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq768 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq768
    | exact resolve eq768 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11753 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq768 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq768
    | (have j0 := eq768 x X0
       grind)
    | exact resolve eq768 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq11851 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11726 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq11726
    | (have j0 := eq11726 X0 X1
       grind)
    | exact resolve eq11726 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq11726
  have eq28548 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (M.op (M.op x X0) (M.op x y)) y) = (k (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have j0 := eq999 X0
       grind)
    | (have r₁ := eq999 X0
       have r₂ := eq7644 X0
       grind)
    | exact resolve eq999 eq7644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq28549 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op x X0) (M.op x y)) y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq7644 eq28548
    | exact resolve eq28548 eq7644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7644 eq28548
  have eq28555 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op X0 x) (M.op x y)) y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq28549 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq62 x X0 x
       grind)
    | exact superpose eq62 eq28549
    | exact resolve eq28549 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28549
  have eq28576 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) = (k (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1003 X0
       grind)
    | (have r₁ := eq1003 X0
       have r₂ := eq7646 X0
       grind)
    | exact resolve eq1003 eq7646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq28577 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq7646 eq28576
    | exact resolve eq28576 eq7646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7646 eq28576
  have eq28859 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28577 (M.op (M.op x x) (M.op x sF2))
       have i₂ := eq62 sF2 x x
       grind)
    | exact superpose eq62 eq28577
    | exact resolve eq28577 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq28577
  have eq52913 : y ≠ (M.op (M.op y y) (M.op x y)) ∨ (M.op y y) = (M.op (M.op y y) (M.op y y)) ∨ y = (k (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq63 eq887
    | exact resolve eq887 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq52935 : (σ y) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq64 eq887
    | exact resolve eq887 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq887
  have eq53309 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have r₁ := eq52935
       have r₂ := eq7654 (σ y) (σ x)
       grind)
    | exact resolve eq52935 eq7654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52935
  have eq53324 : (M.op y y) = (M.op (M.op y y) (M.op y y)) ∨ y = (k (M.op x y) (M.op y y)) := by
    first
    | (have r₁ := eq52913
       have r₂ := eq7654 y x
       grind)
    | exact resolve eq52913 eq7654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7654 eq52913
  have eq53433 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq53309
       have i₂ := eq2139 sF3 sF3
       grind)
    | exact superpose eq2139 eq53309
    | exact resolve eq53309 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53309
  have eq53448 : y = (M.op y y) ∨ y = (k (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq53324
       have i₂ := eq2139 y y
       grind)
    | exact superpose eq2139 eq53324
    | exact resolve eq53324 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139 eq53324
  have eq53540 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq53433
    | exact resolve eq53433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53433
  have eq53547 : y = (k (M.op x y) (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq53448
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53448
    | exact resolve eq53448 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53448
  have eq83914 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11531 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq11531
    | (have j0 := eq11531 (τ X0) X1
       grind)
    | exact resolve eq11531 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq83921 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83914 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq83914
    | (have j0 := eq83914 X0 X1
       grind)
    | exact resolve eq83914 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83914
  have eq83927 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83921 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq83921
    | (have j0 := eq83921 X0 X1
       grind)
    | exact resolve eq83921 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83921
  have eq92135 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11753 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11753
    | (have j0 := eq11753 y
       grind)
    | exact resolve eq11753 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11753
  have eq92311 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq92135
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq92135
    | exact resolve eq92135 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92135
  have eq92328 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq92311
    | exact resolve eq92311 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92311
  have eq93111 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11851 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11851
    | (have j0 := eq11851 X1 X1
       grind)
    | exact resolve eq11851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11851
  have eq93610 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq93111 y x
       grind)
    | exact superpose eq93111 eq72
    | (have j1 := eq93111 x x
       grind)
    | exact resolve eq72 eq93111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq93111
  have eq93890 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq93610
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93610
    | exact resolve eq93610 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93610
  have eq93900 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq93890
    | exact resolve eq93890 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93890
  have eq93914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq93900 eq92328
    | exact resolve eq92328 eq93900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92328 eq93900
  have eq93921 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq93914
       have r₂ := eq27
       grind)
    | exact resolve eq93914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93914
  have eq94035 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq93921 eq2245
    | (have r₁ := eq2245 (σ x) x
       have r₂ := eq93921
       grind)
    | (have r₁ := eq2245 x x
       have r₂ := eq93921
       grind)
    | exact resolve eq2245 eq93921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93921
  have eq94168 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq94035 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94035
  have eq94488 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2245 x X1
       have i₂ := eq94168 X0
       grind)
    | exact superpose eq94168 eq2245
    | (have j1 := eq94168 X1
       grind)
    | (have r₁ := eq2245 x X1
       have r₂ := eq94168 X0
       grind)
    | exact resolve eq2245 eq94168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94168
  have eq94621 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq94488 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94488
  have eq95331 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq94621 (k sF2 sF2) x
       grind)
    | exact superpose eq94621 eq49
    | (have j1 := eq94621 X0 x
       grind)
    | exact resolve eq49 eq94621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq94621
  have eq95418 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq95331
    | (have j0 := eq95331 x
       grind)
    | exact resolve eq95331 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq95331
  have eq95456 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq95418 X0
       have j1 := eq83927 x X0
       grind)
    | (have r₁ := eq95418 X0
       have r₂ := eq83927 x x
       grind)
    | (have r₁ := eq95418 x
       have r₂ := eq83927 x x
       grind)
    | exact resolve eq95418 eq83927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83927 eq95418
  have eq95513 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11531 x X0
       have i₂ := eq95456 x
       grind)
    | exact superpose eq95456 eq11531
    | (have j0 := eq11531 x X0
       grind)
    | exact resolve eq11531 eq95456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11531
  have eq95514 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq109 x
       have i₂ := eq95456 x
       grind)
    | exact superpose eq95456 eq109
    | (have j0 := eq109 x
       grind)
    | exact resolve eq109 eq95456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95456
  have eq95538 : x = (M.op x x) := by grind
  clear eq95514
  have eq95539 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq95513 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95513
  have eq95560 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq95539 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95539
    | (have j0 := eq95539 X0
       grind)
    | exact resolve eq95539 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95539
  have eq95666 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1520 x
       have i₂ := eq95538
       grind)
    | exact superpose eq95538 eq1520
    | exact resolve eq1520 eq95538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq95672 : (M.op x y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq9900 x
       have i₂ := eq95538
       grind)
    | exact superpose eq95538 eq9900
    | exact resolve eq9900 eq95538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9900 eq95538
  have eq95837 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq6150 eq95672
    | exact resolve eq95672 eq6150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6150 eq95672
  have eq95842 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq95666
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95666
    | exact resolve eq95666 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq95666
  have eq95934 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq95560 eq109
    | (have j0 := eq109 (σ x)
       grind)
    | exact resolve eq109 eq95560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq95560
  have eq95958 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq95934
  have eq96696 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq95958 eq1604
    | exact resolve eq1604 eq95958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq96702 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq95958 eq9987
    | exact resolve eq9987 eq95958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9987 eq95958
  have eq96867 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6155 eq96702
    | exact resolve eq96702 eq6155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6155 eq96702
  have eq96872 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq96696
    | exact resolve eq96696 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq96696
  have eq96906 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op X0 x) (M.op x y)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28555 X0
       have i₂ := eq95837
       grind)
    | exact superpose eq95837 eq28555
    | (have j0 := eq28555 X0
       grind)
    | exact resolve eq28555 eq95837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28555
  have eq96937 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96906 (M.op x sF0)
       have i₂ := eq7391 sF0 x
       grind)
    | exact superpose eq7391 eq96906
    | exact resolve eq96906 eq7391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96906
  have eq96942 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq95842 eq96937
    | exact resolve eq96937 eq95842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95842 eq96937
  have eq97546 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq96867 eq28859
    | (have j0 := eq28859 X0
       grind)
    | exact resolve eq28859 eq96867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28859
  have eq97578 : (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97546 (M.op sF2 sF4)
       have i₂ := eq7391 sF4 sF2
       grind)
    | exact superpose eq7391 eq97546
    | exact resolve eq97546 eq7391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7391 eq97546
  have eq97585 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96872 eq97578
    | exact resolve eq97578 eq96872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96872 eq97578
  have eq126563 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq96942
       grind)
    | exact superpose eq96942 eq73
    | exact resolve eq73 eq96942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq96942
  have eq126586 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq126563
    | exact resolve eq126563 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126563
  have eq134889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126586 eq97585
    | exact resolve eq97585 eq126586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134900 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq134889
       have r₂ := eq27
       grind)
    | exact resolve eq134889 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134889
  have eq134929 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134900 eq27
    | exact resolve eq27 eq134900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135079 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134900 eq53540
    | exact resolve eq53540 eq134900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53540
  have eq135099 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq2245 (σ y) (σ y)
       grind)
    | (have r₁ := eq135079
       have r₂ := eq2245 (σ y) x
       grind)
    | exact resolve eq135079 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135079
  have eq135215 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96867 eq135099
    | exact resolve eq135099 eq96867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96867 eq135099
  have eq140718 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134900 eq135215
    | exact resolve eq135215 eq134900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134900 eq135215
  have eq140723 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq140718
  have eq152593 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq140723 eq126586
    | exact resolve eq126586 eq140723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126586 eq140723
  have eq152605 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq152593
  have eq152617 : y = (M.op x y) := by
    first
    | (have r₁ := eq152605
       have r₂ := eq134929
       grind)
    | exact resolve eq152605 eq134929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134929 eq152605
  have eq152634 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq152617 eq20
    | exact resolve eq20 eq152617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq152849 : y = (k y (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq152617 eq53547
    | exact resolve eq53547 eq152617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53547
  have eq152864 : y = (k y (M.op y y)) := by
    first
    | (have j1 := eq2245 y y
       grind)
    | (have r₁ := eq152849
       have r₂ := eq2245 y x
       grind)
    | exact resolve eq152849 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245 eq152849
  have eq153007 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq152634
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq152634
    | exact resolve eq152634 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152634
  have eq153008 : y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq152864
       have i₂ := eq95837
       grind)
    | exact superpose eq95837 eq152864
    | exact resolve eq152864 eq95837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95837 eq152864
  have eq153090 : y = (k y y) := by
    first
    | exact superpose eq152617 eq153008
    | exact resolve eq153008 eq152617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153008
  have eq153421 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153007 eq97585
    | exact resolve eq97585 eq153007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97585
  have eq153431 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq153421
       have r₂ := eq27
       grind)
    | exact resolve eq153421 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153421
  have eq153769 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq153431 eq148
    | exact resolve eq148 eq153431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq153431
  have eq153794 : (k y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq152617 eq153769
    | exact resolve eq153769 eq152617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152617 eq153769
  have eq153810 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq153794
       have i₂ := eq153090
       grind)
    | exact superpose eq153090 eq153794
    | exact resolve eq153794 eq153090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153090 eq153794
  have eq153826 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153810 eq15
    | exact resolve eq15 eq153810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153810
  have eq153921 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq153826
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq153826
    | exact resolve eq153826 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq153826
  have eq153949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153007 eq153921
    | exact resolve eq153921 eq153007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153007 eq153921
  have eq153966 : False := by grind
  exact eq153966

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxy_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
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
  have eq57 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq58 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
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
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq97 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq93
  have eq98 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
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
  have eq104 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
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
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq131 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq55 X1 x x X0
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq580 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq239 eq56
    | exact resolve eq56 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq584 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq244 eq56
    | exact resolve eq56 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq594 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq597 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq786 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq59 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1750 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq526 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq526
    | exact resolve eq526 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq1976 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq535 X1 X0
       grind)
    | exact superpose eq535 eq14
    | exact resolve eq14 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3082 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq580 eq594
    | exact resolve eq594 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq594
  have eq3112 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq3082 X0
       have i₂ := eq535 y (M.op x X0)
       grind)
    | exact superpose eq535 eq3082
    | exact resolve eq3082 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq3196 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq584 eq597
    | exact resolve eq597 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq597
  have eq3224 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3196 X0
       have i₂ := eq535 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq535 eq3196
    | exact resolve eq3196 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq3196
  have eq6627 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq3112 eq565
    | exact resolve eq565 eq3112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq6632 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq3224 eq565
    | exact resolve eq565 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq3224
  have eq7853 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0 X1
       grind)
    | exact superpose eq56 eq786
    | exact resolve eq786 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq786
  have eq7977 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7853 X0 X1
       have i₂ := eq1976 X0 X0
       grind)
    | exact superpose eq1976 eq7853
    | exact resolve eq7853 eq1976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976 eq7853
  have eq8124 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq241 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq7977 (M.op x X0) y
       grind)
    | exact superpose eq7977 eq241
    | exact resolve eq241 eq7977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq8126 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq246 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq7977 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq7977 eq246
    | exact resolve eq246 eq7977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq7977
  have eq8946 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq8124 (M.op x (M.op X0 x))
       have i₂ := eq1750 x X0
       grind)
    | exact superpose eq1750 eq8124
    | exact resolve eq8124 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8124
  have eq9007 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8126 (M.op sF2 (M.op x sF2))
       have i₂ := eq1750 sF2 x
       grind)
    | exact superpose eq1750 eq8126
    | exact resolve eq8126 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750 eq8126
  have eq58224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq58224
    | exact resolve eq58224 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58224
  have eq58239 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq58234
       have r₂ := eq28
       grind)
    | exact resolve eq58234 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58234
  have eq58251 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq58239 eq9007
    | exact resolve eq9007 eq58239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58255 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq58239 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq58239
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq58239
       grind)
    | exact resolve eq12 eq58239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58239
  have eq58360 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq58255
  have eq58361 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq58360
  have eq58365 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq6632 eq58251
    | exact resolve eq58251 eq6632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58251
  have eq61591 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq58361 eq106
    | exact resolve eq106 eq58361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq61594 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq58361 eq104
    | exact resolve eq104 eq58361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq58361
  have eq61606 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq61591
  have eq61609 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq131 eq61594
    | exact resolve eq61594 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq61594
  have eq61612 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq12 (k y x) (M.op y y)
       grind)
    | (have r₁ := eq61609
       have r₂ := eq12 y x
       grind)
    | exact resolve eq61609 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61609
  have eq61614 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq61612
       grind)
    | exact superpose eq61612 eq92
    | exact resolve eq92 eq61612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq61612
  have eq61648 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61614
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq61614
    | exact resolve eq61614 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61614
  have eq61700 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq61648 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq61648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61648
  have eq61710 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq61700
  have eq61714 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq61710
    | exact resolve eq61710 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61710
  have eq61733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq61606 eq58365
    | exact resolve eq58365 eq61606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58365 eq61606
  have eq61858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq61733
  have eq61862 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61858
       have r₂ := eq28
       grind)
    | exact resolve eq61858 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61858
  have eq61877 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8946 y
       have i₂ := eq61862
       grind)
    | exact superpose eq61862 eq8946
    | exact resolve eq8946 eq61862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8946 eq61862
  have eq61991 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6627 eq61877
    | exact resolve eq61877 eq6627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6627 eq61877
  have eq62184 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq98
       have i₂ := eq61991
       grind)
    | exact superpose eq61991 eq98
    | exact resolve eq98 eq61991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq61991
  have eq62347 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq62184
    | exact resolve eq62184 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62184
  have eq137574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq61714 eq62347
    | exact resolve eq62347 eq61714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61714
  have eq137772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq137574
  have eq137786 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq137772
       have r₂ := eq28
       grind)
    | exact resolve eq137772 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137772
  have eq137818 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq137786 eq9007
    | exact resolve eq9007 eq137786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9007 eq137786
  have eq137944 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6632 eq137818
    | exact resolve eq137818 eq6632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6632 eq137818
  have eq138994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq137944 eq62347
    | exact resolve eq62347 eq137944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62347 eq137944
  have eq139193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq138994
  have eq139207 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq139193
       have r₂ := eq28
       grind)
    | exact resolve eq139193 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139193
  have eq139210 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq139207 eq30
    | exact resolve eq30 eq139207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq139207
  have eq139357 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq139210
    | exact resolve eq139210 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq139210
  have eq139358 : x = y := by grind
  clear eq139357
  have eq139873 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq139358
       grind)
    | exact superpose eq139358 eq19
    | exact resolve eq19 eq139358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq139874 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq139358
       grind)
    | exact superpose eq139358 eq25
    | exact resolve eq25 eq139358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq139358
  have eq140097 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq139874
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq139874
    | exact resolve eq139874 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq139874
  have eq140116 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq140097 eq27
    | exact resolve eq27 eq140097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq140097
  have eq140548 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq140116 eq71
    | exact resolve eq71 eq140116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq140116
  have eq140742 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq140548
       have i₂ := eq139873
       grind)
    | exact superpose eq139873 eq140548
    | exact resolve eq140548 eq139873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139873 eq140548
  have eq140748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140742 eq15
    | exact resolve eq15 eq140742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140742
  have eq140838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq140748
    | exact resolve eq140748 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq140748
  have eq140859 : False := by grind
  exact eq140859
