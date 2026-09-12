import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pxy_y_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = (k y x) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq99 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq103 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq99
    | exact resolve eq99 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq103
    | exact resolve eq103 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq98
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  clear eq50
  have eq243 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq582 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq855 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq895 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq856 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq856
    | (have j0 := eq856 y X0
       grind)
    | exact resolve eq856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq918 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq895 X0
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq895
    | (have j0 := eq895 X0
       grind)
    | exact resolve eq895 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq895
  have eq1069 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq582
    | (have j0 := eq582 (σ x) (σ y) X0
       grind)
    | exact resolve eq582 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq582 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq582
    | (have j0 := eq582 x X0 y
       grind)
    | exact resolve eq582 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq582
    | (have j0 := eq582 (σ x) X0 (σ y)
       grind)
    | exact resolve eq582 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq582 X0 X1 x
       grind)
    | exact superpose eq582 eq14
    | exact resolve eq14 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1157 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1088 (σ X0) X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1088
    | exact resolve eq1088 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1160 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1088 X0 (M.op X0 X1)
       have i₂ := eq582 X0 X0 X1
       grind)
    | exact superpose eq582 eq1088
    | exact resolve eq1088 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1165 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1088 (M.op X0 X1) X0
       grind)
    | exact superpose eq1088 eq55
    | exact resolve eq55 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1170 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1088 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1088 eq14
    | exact resolve eq14 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1185 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1165 X0 X1
       have i₂ := eq582 X0 X1 X1
       grind)
    | exact superpose eq582 eq1165
    | exact resolve eq1165 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1270 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1083 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1083
    | (have j0 := eq1083 y
       grind)
    | exact resolve eq1083 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1454 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1084
    | (have j0 := eq1084 (σ y)
       grind)
    | exact resolve eq1084 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1490 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1069 eq1454
    | exact resolve eq1454 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1752 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq236 eq1160
    | exact resolve eq1160 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1754 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1454 eq1160
    | exact resolve eq1160 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1758 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq243 eq1160
    | exact resolve eq1160 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1789 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1758
       have i₂ := eq1088 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1088 eq1758
    | exact resolve eq1758 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq1793 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1754
       have i₂ := eq1088 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1088 eq1754
    | exact resolve eq1754 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754
  have eq1795 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1752
       have i₂ := eq1088 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1088 eq1752
    | exact resolve eq1752 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq1837 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1789 eq243
    | exact resolve eq243 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1921 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1795 eq236
    | exact resolve eq236 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2119 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1789 eq1793
    | exact resolve eq1793 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq2846 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1185 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1185
    | exact resolve eq1185 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2848 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq236 eq1185
    | exact resolve eq1185 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2850 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq243 eq1185
    | exact resolve eq1185 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq2854 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1185 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1160 X0 X1
       grind)
    | exact superpose eq1160 eq1185
    | exact resolve eq1185 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq2931 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2854 X0 X1
       have i₂ := eq1170 X0 X0
       grind)
    | exact superpose eq1170 eq2854
    | exact resolve eq2854 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170 eq2854
  have eq2937 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2931 X0 X1
       have i₂ := eq582 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq582 eq2931
    | exact resolve eq2931 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931
  have eq2938 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2937 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2937
    | exact resolve eq2937 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2937
  have eq3382 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq2848 eq2938
    | exact resolve eq2938 eq2848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3397 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2938 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2938
    | (have j0 := eq2938 x y
       grind)
    | exact resolve eq2938 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3403 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2938
    | (have j0 := eq2938 (σ x) (σ y)
       grind)
    | exact resolve eq2938 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq3472 : (M.op (M.op (M.op x y) (M.op x y)) y) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq3382
       have i₂ := eq582 sF0 y y
       grind)
    | exact superpose eq582 eq3382
    | exact resolve eq3382 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq3508 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq236 eq3472
    | exact resolve eq3472 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq3472
  have eq3539 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq3397 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq3397
       grind)
    | exact resolve eq12 eq3397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3397
  have eq3552 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq3539
  have eq3556 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1795 eq3552
    | exact resolve eq3552 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq3561 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3403 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq3403
       grind)
    | exact resolve eq12 eq3403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq3574 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq3561
  have eq3578 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1789 eq3574
    | exact resolve eq3574 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3574
  have eq4033 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2846 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2846 X0 X1
       grind)
    | exact superpose eq2846 eq2846
    | exact resolve eq2846 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4140 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4033 X0 X1
       have i₂ := eq1185 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1185 eq4033
    | exact resolve eq4033 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185 eq4033
  have eq4178 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4140 X0 X1
       have i₂ := eq582 X0 X0 X1
       grind)
    | exact superpose eq582 eq4140
    | exact resolve eq4140 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq4140
  have eq4496 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1490 eq246
    | (have j0 := eq246 (σ y) X1
       grind)
    | exact resolve eq246 eq1490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq1490
  have eq4497 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1789 eq4496
    | exact resolve eq4496 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4496
  have eq4602 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4497 eq2846
    | exact resolve eq2846 eq4497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq4608 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1837 eq4602
    | exact resolve eq4602 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4602
  have eq4615 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2119 eq4608
    | exact resolve eq4608 eq2119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119 eq4608
  have eq6648 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4178 X0 X2
       have i₂ := eq4178 X0 X1
       grind)
    | (have i₁ := eq4178 X1 X1
       have i₂ := eq4178 X1 X1
       grind)
    | exact superpose eq4178 eq4178
    | exact resolve eq4178 eq4178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4178
  have eq7222 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq918 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq918
    | (have j0 := eq918 x
       grind)
    | exact resolve eq918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq7252 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7222
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq7222
    | exact resolve eq7222 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7222
  have eq7270 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq7252
    | exact resolve eq7252 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7252
  have eq7281 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq7270
    | exact resolve eq7270 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7270
  have eq7290 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7281
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq7281
    | exact resolve eq7281 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7281
  have eq7298 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq7290
    | exact resolve eq7290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7290
  have eq9823 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq3508 eq6648
    | exact resolve eq6648 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508 eq6648
  have eq45012 : x = (M.op (M.op x x) y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq3556 eq1921
    | exact resolve eq1921 eq3556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921 eq3556
  have eq45123 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq45012
       have i₂ := eq1270
       grind)
    | exact superpose eq1270 eq45012
    | exact resolve eq45012 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270 eq45012
  have eq45136 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1795 eq45123
    | exact resolve eq45123 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795 eq45123
  have eq45532 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3578 eq1837
    | exact resolve eq1837 eq3578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837 eq3578
  have eq45631 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1454 eq45532
    | exact resolve eq45532 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454 eq45532
  have eq45644 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1789 eq45631
    | exact resolve eq45631 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq45631
  have eq52570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq52579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq52570
    | exact resolve eq52570 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52570
  have eq52590 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq52579
       have r₂ := eq27
       grind)
    | exact resolve eq52579 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52579
  have eq52594 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq52590
    | exact resolve eq52590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52590
  have eq52598 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq52594
    | exact resolve eq52594 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52594
  have eq52616 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq52598 eq1088
    | exact resolve eq1088 eq52598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52598
  have eq56925 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq52616 eq4615
    | exact resolve eq4615 eq52616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4615 eq52616
  have eq57052 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq56925
    | exact resolve eq56925 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56925
  have eq57053 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq57052
  have eq57094 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq57053 eq78
    | (have r₁ := eq78
       have r₂ := eq57053
       grind)
    | exact resolve eq78 eq57053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq57053
  have eq57196 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq57094
  have eq75151 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq57196 eq2846
    | exact resolve eq2846 eq57196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57196
  have eq75164 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2850 eq75151
    | exact resolve eq75151 eq2850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75151
  have eq75182 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq75164 eq112
    | exact resolve eq112 eq75164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq75164
  have eq75214 : x = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq28 eq75182
    | exact resolve eq75182 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75182
  have eq75224 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq75214
       have r₂ := eq77
       grind)
    | exact resolve eq75214 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq75214
  have eq75577 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1088 y X0
       have i₂ := eq75224
       grind)
    | exact superpose eq75224 eq1088
    | exact resolve eq1088 eq75224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq75224
  have eq77028 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq75577 eq9823
    | exact resolve eq9823 eq75577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9823 eq75577
  have eq83108 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1157 y X0
       have i₂ := eq77028
       grind)
    | exact superpose eq77028 eq1157
    | exact resolve eq1157 eq77028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77028
  have eq83184 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq83108 x
       have i₂ := eq1157 x x
       grind)
    | exact superpose eq1157 eq83108
    | exact resolve eq83108 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157 eq83108
  have eq83216 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq83184
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq83184
    | exact resolve eq83184 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83184
  have eq83224 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq83216
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq83216
    | exact resolve eq83216 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83216
  have eq83225 : x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq83224
  have eq83561 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq83225
       grind)
    | exact superpose eq83225 eq98
    | exact resolve eq98 eq83225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq83571 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq83225
       grind)
    | exact superpose eq83225 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq83225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83225
  have eq83587 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83571
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83571
    | exact resolve eq83571 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83571
  have eq83597 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83561
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq83561
    | exact resolve eq83561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83561
  have eq83606 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83587
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83587
    | exact resolve eq83587 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83587
  have eq83617 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83606
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83606
    | exact resolve eq83606 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83606
  have eq83677 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7298 eq83597
    | exact resolve eq83597 eq7298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7298 eq83597
  have eq153958 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2846 y y
       have i₂ := eq83617
       grind)
    | exact superpose eq83617 eq2846
    | exact resolve eq2846 eq83617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83617
  have eq153974 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2848 eq153958
    | exact resolve eq153958 eq2848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848 eq153958
  have eq154014 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq153974
       grind)
    | exact superpose eq153974 eq72
    | exact resolve eq72 eq153974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153974
  have eq154210 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq154014
    | exact resolve eq154014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154014
  have eq166085 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq83677 eq2846
    | exact resolve eq2846 eq83677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846 eq83677
  have eq166104 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2850 eq166085
    | exact resolve eq166085 eq2850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2850 eq166085
  have eq166105 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq166104
  have eq166161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq166105 eq154210
    | exact resolve eq154210 eq166105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq166161
  have eq166306 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq166254
       have r₂ := eq27
       grind)
    | exact resolve eq166254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166254
  have eq167283 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq166306 eq27
    | exact resolve eq27 eq166306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167354 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq166306 eq45644
    | exact resolve eq45644 eq166306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45644 eq166306
  have eq167494 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq167354
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq167354
    | exact resolve eq167354 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167354
  have eq167495 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq167494
  have eq172772 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq167495 eq154210
    | exact resolve eq154210 eq167495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154210 eq167495
  have eq172875 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq172772
  have eq172939 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq172875
       have r₂ := eq167283
       grind)
    | exact resolve eq172875 eq167283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167283 eq172875
  have eq173008 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq172939 eq29
    | exact resolve eq29 eq172939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172939
  have eq173225 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq173008
    | exact resolve eq173008 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173008
  have eq173226 : x = (M.op x y) ∨ x = y := by grind
  clear eq173225
  have eq173782 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq173226 eq20
    | exact resolve eq20 eq173226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173985 : x = (k x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq173226 eq45136
    | exact resolve eq45136 eq173226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45136 eq173226
  have eq174068 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq173985
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq173985
    | exact resolve eq173985 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq173985
  have eq174069 : x = (M.op x x) ∨ x = y := by grind
  clear eq174068
  have eq174237 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq173782
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq173782
    | exact resolve eq173782 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173782
  have eq175463 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq174069
       grind)
    | exact superpose eq174069 eq72
    | exact resolve eq72 eq174069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq174069
  have eq175685 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq175463
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq175463
    | exact resolve eq175463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175463
  have eq178795 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq175685 eq166105
    | exact resolve eq166105 eq175685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166105 eq175685
  have eq178897 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq178795
  have eq189206 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq178897 eq27
    | exact resolve eq27 eq178897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178897
  have eq189512 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq189206
       have r₂ := eq174237
       grind)
    | exact resolve eq189206 eq174237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174237 eq189206
  have eq189581 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq189512 eq29
    | exact resolve eq29 eq189512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq189512
  have eq189801 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq189581
    | exact resolve eq189581 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq189581
  have eq189802 : x = y := by grind
  clear eq189801
  have eq189833 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq189802
       grind)
    | exact superpose eq189802 eq18
    | exact resolve eq18 eq189802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq189834 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq189802
       grind)
    | exact superpose eq189802 eq24
    | exact resolve eq24 eq189802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq189802
  have eq190302 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq189834
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq189834
    | exact resolve eq189834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq189834
  have eq190382 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq190302 eq26
    | exact resolve eq26 eq190302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq190302
  have eq190941 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq190382 eq71
    | exact resolve eq71 eq190382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq190382
  have eq191147 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq190941
       have i₂ := eq189833
       grind)
    | exact superpose eq189833 eq190941
    | exact resolve eq190941 eq189833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189833 eq190941
  have eq191234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq191147 eq15
    | exact resolve eq15 eq191147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191147
  have eq191578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq191234
    | exact resolve eq191234 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq191234
  have eq191685 : False := by grind
  exact eq191685

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq24 eq35
  have eq78 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq44
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq44 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq131
  have eq500 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq499
  have eq763 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq500 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq500
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq500
       grind)
    | exact resolve eq13 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq770 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq763
  have eq776 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq770
    | exact resolve eq770 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq776
    | exact resolve eq776 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq776
  have eq789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq781
  have eq792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq789
       have r₂ := eq133
       grind)
    | exact resolve eq789 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq789
  have eq793 : x = (M.op x y) := by
    first
    | (have r₁ := eq792
       have r₂ := eq27
       grind)
    | exact resolve eq792 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq794 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq793 eq20
    | exact resolve eq20 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq800 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq793 eq78
    | (have r₁ := eq78
       have r₂ := eq793
       grind)
    | exact resolve eq78 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq806 : y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq800
  have eq814 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq794
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq794
    | exact resolve eq794 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq867 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq814 eq26
    | exact resolve eq26 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1724 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq806
       grind)
    | exact resolve eq13 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq1736 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq1724
  have eq1739 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1736
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1736
    | exact resolve eq1736 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1736
  have eq1744 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq793 eq1739
    | exact resolve eq1739 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq1739
  have eq1745 : x = (k x y) := by grind
  clear eq1744
  have eq1750 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1745
       grind)
    | exact superpose eq1745 eq44
    | exact resolve eq44 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1745
  have eq1757 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq814 eq1750
    | exact resolve eq1750 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1759 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1757
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1757
    | exact resolve eq1757 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1757
  have eq1760 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq814 eq1759
    | exact resolve eq1759 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1759
  have eq1810 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1760 eq96
    | (have j0 := eq96 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq96 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1760
  have eq1811 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1810
  have eq1813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq867 eq1811
    | exact resolve eq1811 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867 eq1811
  have eq1816 : False := by grind
  exact eq1816

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_y_pyx_x_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X1 X1)
       have r₂ := eq13 X0 X1
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X2 X0)) X2) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
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
  have eq189 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq194 : x = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 x
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq199 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x (M.op X1 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq215 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (M.op X1 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq178 (M.op (M.op X0 X1) (M.op y X1))
       have i₂ := eq16 X0 X1 y
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op X0 (M.op X1 x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ y) X1)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 (M.op (M.op X0 X1) (M.op sF3 X1))
       have i₂ := eq16 X0 X1 sF3
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq188
       grind)
    | exact superpose eq188 eq40
    | exact resolve eq40 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq452 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq451
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq451
    | exact resolve eq451 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq454 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq452
    | exact resolve eq452 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq454 eq189
    | exact resolve eq189 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq454
  have eq550 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq543
       have r₂ := eq27
       grind)
    | exact resolve eq543 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq558 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq550 eq16
    | exact resolve eq16 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op X0 (σ y))) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq550 eq16
    | exact resolve eq16 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq215 eq559
    | exact resolve eq559 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq559
  have eq563 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq550 eq560
    | exact resolve eq560 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq567 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq563 eq16
    | exact resolve eq16 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq616 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq550 eq558
    | exact resolve eq558 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq624 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq616
  have eq655 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq558 eq567
    | exact resolve eq567 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq682 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq624 eq567
    | exact resolve eq567 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq624
  have eq688 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq682
  have eq689 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq681 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq697 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (k y y) := by
    first
    | (have i₁ := eq688
       have i₂ := eq655 y
       grind)
    | exact superpose eq655 eq688
    | exact resolve eq688 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq698 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq689 X0
       have i₂ := eq655 y
       grind)
    | exact superpose eq655 eq689
    | (have j0 := eq689 X0
       grind)
    | exact resolve eq689 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq736 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq698 eq697
    | exact resolve eq697 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq698
  have eq738 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) := by grind
  clear eq736
  have eq740 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq738
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq738
    | exact resolve eq738 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq757 : (τ (σ x)) = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq740 eq116
    | exact resolve eq116 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq740
  have eq764 : x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq757
    | exact resolve eq757 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq757
  have eq765 : x = (k y y) := by grind
  clear eq764
  have eq772 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq41
    | exact resolve eq41 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq775 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq772
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq772
    | exact resolve eq772 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq778 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq775
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq775
    | exact resolve eq775 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq1394 : y = (M.op (M.op (k y y) (M.op x y)) x) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq655 y
       grind)
    | exact superpose eq655 eq178
    | exact resolve eq178 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1395 : x = (M.op (M.op (M.op x y) (k y y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq655 y
       grind)
    | exact superpose eq655 eq175
    | exact resolve eq175 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1398 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq176 sF3
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq176
    | exact resolve eq176 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : (σ y) = (M.op (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq179 sF3
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq179
    | exact resolve eq179 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1429 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq778 eq1399
    | exact resolve eq1399 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1430 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq778 eq1398
    | exact resolve eq1398 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1432 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq1395
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq1395
    | exact resolve eq1395 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1433 : y = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq1394
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq1394
    | exact resolve eq1394 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq1451 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (k X0 X0)) = (M.op (M.op X1 (M.op X2 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 X0 X0 X2
       have i₂ := eq655 X0
       grind)
    | exact superpose eq655 eq177
    | exact resolve eq177 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1494 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) X1)) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq210 eq177
    | exact resolve eq177 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1542 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ y) X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op X0 (M.op sF3 X2))
       have i₂ := eq177 X0 X1 X2 sF3
       grind)
    | exact superpose eq177 eq179
    | exact resolve eq179 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1583 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) X1)) = (M.op (M.op X0 (σ x)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1494 X0 X1
       have i₂ := eq655 sF4
       grind)
    | exact superpose eq655 eq1494
    | exact resolve eq1494 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1651 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1430 eq179
    | exact resolve eq179 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1667 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1429 eq1651
    | exact resolve eq1651 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq1690 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq1667 eq16
    | exact resolve eq16 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1691 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op X0 (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq1667 eq16
    | exact resolve eq16 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1692 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq242 eq1691
    | exact resolve eq1691 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq1691
  have eq1698 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1692
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq1692
    | exact resolve eq1692 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq1701 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq778 eq1698
    | exact resolve eq1698 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1710 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1701 eq177
    | exact resolve eq177 eq1701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1712 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq1701 eq16
    | exact resolve eq16 eq1701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701
  have eq1724 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq1432 eq178
    | exact resolve eq178 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1734 : y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1433 eq1724
    | exact resolve eq1724 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq1746 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op X0 X1) (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq1734 eq177
    | exact resolve eq177 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1747 : y = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1734 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1748 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq1734 eq16
    | exact resolve eq16 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1749 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op X0 x)) X0) := by
    intro X0
    first
    | exact superpose eq1734 eq16
    | exact resolve eq16 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1750 : (M.op x y) = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq1749 x
       have i₂ := eq232 y x
       grind)
    | exact superpose eq232 eq1749
    | exact resolve eq1749 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq1749
  have eq1751 : (M.op x y) = (k x x) ∨ y = (k x (M.op x y)) := by
    first
    | (have i₁ := eq1747
       have i₂ := eq655 x
       grind)
    | exact superpose eq655 eq1747
    | exact resolve eq1747 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq1754 : (M.op x y) = (M.op (k y y) (M.op x y)) := by
    first
    | (have i₁ := eq1750
       have i₂ := eq655 y
       grind)
    | exact superpose eq655 eq1750
    | exact resolve eq1750 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1755 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1754
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq1754
    | exact resolve eq1754 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754
  have eq1759 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) x) = X0 := by
    intro X0
    first
    | exact superpose eq1755 eq16
    | exact resolve eq16 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1795 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1690 sF2
       have i₂ := eq655 sF2
       grind)
    | exact superpose eq655 eq1690
    | exact resolve eq1690 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 (σ x)) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1690 eq177
    | exact resolve eq177 eq1690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1834 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (σ x)) (σ y))) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq1710 eq1828
    | exact resolve eq1828 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1861 : x = (M.op (M.op (k x x) y) (M.op x y)) := by
    first
    | (have i₁ := eq1748 x
       have i₂ := eq655 x
       grind)
    | exact superpose eq655 eq1748
    | exact resolve eq1748 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1894 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op (σ x) (σ y))) (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1712 (M.op X0 (M.op sF4 X2))
       have i₂ := eq177 X0 X1 X2 sF4
       grind)
    | exact superpose eq177 eq1712
    | exact resolve eq1712 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq1690 eq1712
    | exact resolve eq1712 eq1690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1926 : ∀ X0 X2 : G, (M.op X0 (M.op (σ y) X2)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X2)) := by
    intro X0 X2
    first
    | exact superpose eq1542 eq1894
    | exact resolve eq1894 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542 eq1894
  have eq1948 : (M.op x y) = (M.op (M.op (k (M.op x y) (M.op x y)) (M.op x y)) x) := by
    first
    | (have i₁ := eq1759 sF0
       have i₂ := eq655 sF0
       grind)
    | exact superpose eq655 eq1759
    | exact resolve eq1759 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1949 : (M.op (M.op x (M.op x y)) x) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq175 eq1759
    | exact resolve eq1759 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1759 eq1748
    | exact resolve eq1748 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq1969 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq1433 eq1949
    | exact resolve eq1949 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433 eq1949
  have eq1981 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) y)) y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq1969 eq16
    | exact resolve eq16 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1984 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) y)) (M.op x y)) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq1958 eq1981
    | exact resolve eq1981 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq1993 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (k y y)) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1984 x
       have i₂ := eq1451 y x sF0
       grind)
    | exact superpose eq1451 eq1984
    | exact resolve eq1984 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451 eq1984
  have eq1999 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1993 X0
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq1993
    | exact resolve eq1993 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765 eq1993
  have eq2019 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1795 eq1712
    | exact resolve eq1712 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2037 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq236 eq2019
    | exact resolve eq2019 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2045 : (M.op (k (σ x) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq2037
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq2037
    | exact resolve eq2037 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037
  have eq2049 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq778 eq2045
    | exact resolve eq2045 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq2052 : (σ y) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1667 eq2049
    | exact resolve eq2049 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667 eq2049
  have eq2056 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2052 eq1795
    | exact resolve eq1795 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2057 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq2052 eq176
    | exact resolve eq176 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2058 : (k (σ x) (σ x)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq2052 eq179
    | exact resolve eq179 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2074 : (k (σ x) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq1896 eq2058
    | exact resolve eq2058 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq2092 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2056 eq16
    | exact resolve eq16 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2095 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1896 eq2092
    | exact resolve eq2092 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq2110 : ∀ X0 : G, (M.op (k x x) y) = (M.op (M.op x (M.op X0 (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq1861 eq16
    | exact resolve eq16 eq1861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq2111 : (M.op (k x x) y) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq2110 x
       have i₂ := eq199 sF0 x
       grind)
    | exact superpose eq199 eq2110
    | exact resolve eq2110 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq2110
  have eq2117 : y = (M.op (k x x) y) := by
    first
    | exact superpose eq1969 eq2111
    | exact resolve eq2111 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969 eq2111
  have eq2125 : x = (M.op (M.op (M.op x y) y) (k x x)) := by
    first
    | (have i₁ := eq175 (k x x)
       have i₂ := eq2117
       grind)
    | exact superpose eq2117 eq175
    | exact resolve eq175 eq2117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2117
  have eq2190 : (M.op (M.op x y) x) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq1432 eq1999
    | exact resolve eq1999 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq2206 : (M.op (M.op x y) x) = (M.op (k x x) (M.op x y)) := by
    first
    | (have i₁ := eq2190
       have i₂ := eq655 x
       grind)
    | exact superpose eq655 eq2190
    | exact resolve eq2190 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190
  have eq2216 : y = (M.op (k x x) (M.op x y)) := by
    first
    | exact superpose eq1734 eq2206
    | exact resolve eq2206 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2243 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op X0 X1) (M.op (k (σ x) (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq2057 eq177
    | exact resolve eq177 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2253 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (k (σ x) (σ x)) X1)) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1926 eq2243
    | exact resolve eq2243 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq2258 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (k (σ x) (σ x)) X1)) = (M.op (M.op X0 (σ x)) (k (σ y) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2253 X0 X1
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq2253
    | exact resolve eq2253 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq2262 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op X0 X1) (M.op (k (σ x) (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq778 eq2258
    | exact resolve eq2258 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2258
  have eq2304 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) X1) (M.op (M.op X1 X2) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq176 eq180
    | exact resolve eq180 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2327 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) (M.op (M.op X0 X1) (M.op (k (σ x) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq2057 eq180
    | exact resolve eq180 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2373 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op (M.op x y) X1) (M.op x X1))) := by
    intro X0 X1
    first
    | exact superpose eq1999 eq180
    | exact resolve eq180 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2400 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) X1) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq180
    | exact resolve eq180 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2401 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (σ x) X1) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq1712 eq180
    | exact resolve eq180 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2403 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq1429 eq180
    | exact resolve eq180 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2416 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) (M.op (σ x) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq176 eq180
    | exact resolve eq180 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2482 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) X2) (M.op (M.op X2 X1) (σ x))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq176 eq180
    | exact resolve eq180 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2512 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (k (σ x) (σ x)) (σ y))) X1) (M.op (M.op X1 (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1795 eq180
    | exact resolve eq180 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq2520 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X1) (M.op (M.op X1 (σ x)) (σ x))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq210 eq180
    | exact resolve eq180 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2550 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq180 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2581 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2520 X0 X1
       have i₂ := eq2550 (M.op (M.op X0 (M.op sF4 sF4)) X1) X1 sF2
       grind)
    | exact superpose eq2550 eq2520
    | exact resolve eq2520 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520
  have eq2588 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (k (σ x) (σ x)) (σ y))) X1) (M.op (M.op X1 (σ x)) (σ y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1896 eq2512
    | exact resolve eq2512 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2610 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (σ y) (M.op X1 (σ y)))) X2) (M.op (M.op X2 X1) (σ x))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq1926 eq2482
    | exact resolve eq2482 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq2646 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (σ y) (M.op X2 (σ y)))) (M.op (σ x) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq1926 eq2416
    | exact resolve eq2416 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq2653 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x))) := by
    first
    | exact superpose eq1710 eq2403
    | exact resolve eq2403 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq2655 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq1710 eq2401
    | exact resolve eq2401 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2656 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq1710 eq2400
    | exact resolve eq2400 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710 eq2400
  have eq2679 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op (M.op x y) y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2373 X0 y
       have i₂ := eq1746 sF0 x
       grind)
    | (have i₁ := eq2373 X0 x
       have i₂ := eq1746 sF0 x
       grind)
    | exact superpose eq1746 eq2373
    | (have j0 := eq2373 X0 y
       grind)
    | exact resolve eq2373 eq1746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746 eq2373
  have eq2714 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) (M.op (M.op X0 (σ x)) (σ x))) := by
    intro X0
    first
    | exact superpose eq2262 eq2327
    | exact resolve eq2327 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327
  have eq2742 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X1) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1926 eq2581
    | exact resolve eq2581 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2581
  have eq2746 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (k (σ x) (σ x)) (σ y))) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq1834 eq2588
    | exact resolve eq2588 eq1834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834 eq2588
  have eq2774 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq236 eq2653
    | exact resolve eq2653 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2653
  have eq2776 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq236 eq2655
    | exact resolve eq2655 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq2777 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq236 eq2656
    | exact resolve eq2656 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq2656
  have eq2797 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1958 eq2679
    | exact resolve eq2679 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq2679
  have eq2824 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2714 x
       have i₂ := eq2550 (M.op sF2 x) x sF2
       grind)
    | exact superpose eq2550 eq2714
    | exact resolve eq2714 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714
  have eq2846 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) X1) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq2056 eq2742
    | exact resolve eq2742 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056 eq2742
  have eq2849 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (k (σ x) (σ x)) (σ y))) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1896 eq2746
    | exact resolve eq2746 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746
  have eq2858 : (σ x) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq1926 eq2774
    | exact resolve eq2774 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq2860 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1926 eq2776
    | exact resolve eq2776 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2776
  have eq2861 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1926 eq2777
    | exact resolve eq2777 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq2878 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2797 X0
       have i₂ := eq2550 X0 sF0 sF0
       grind)
    | exact superpose eq2550 eq2797
    | exact resolve eq2797 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797
  have eq2911 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2052 eq2849
    | exact resolve eq2849 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052 eq2849
  have eq2918 : (σ x) = (M.op (σ y) (M.op (σ y) (k (σ y) (σ y)))) := by
    first
    | (have i₁ := eq2858
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq2858
    | exact resolve eq2858 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq2920 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (k (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2860 X0
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq2860
    | exact resolve eq2860 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq2921 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (k (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2861 X0
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq2861
    | exact resolve eq2861 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861
  have eq2952 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) := by
    first
    | exact superpose eq778 eq2918
    | exact resolve eq2918 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2918
  have eq2954 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq778 eq2920
    | exact resolve eq2920 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2920
  have eq2955 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq778 eq2921
    | exact resolve eq2921 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq3264 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op (M.op X0 X1) (M.op (M.op (σ y) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq2952 eq180
    | exact resolve eq180 eq2952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952
  have eq3271 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ x)) (σ y))) := by
    first
    | exact superpose eq2304 eq3264
    | exact resolve eq3264 eq2304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304 eq3264
  have eq3281 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq2074 eq3271
    | exact resolve eq3271 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3303 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (M.op (k (σ x) (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3281 eq177
    | exact resolve eq177 eq3281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3304 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (M.op X0 X1) (M.op (k (σ x) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq3281 eq180
    | exact resolve eq180 eq3281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq3309 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (M.op X0 (σ x)) (σ x))) := by
    intro X0
    first
    | exact superpose eq2262 eq3304
    | exact resolve eq3304 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304
  have eq3310 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2262 eq3303
    | exact resolve eq3303 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262 eq3303
  have eq3317 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3309 x
       have i₂ := eq2550 (M.op sF3 x) x sF2
       grind)
    | exact superpose eq2550 eq3309
    | exact resolve eq3309 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550 eq3309
  have eq3332 : (σ y) = (M.op (M.op (σ x) (σ y)) x) := by
    first
    | exact superpose eq3317 eq1759
    | exact resolve eq1759 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3406 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq3332 eq16
    | exact resolve eq16 eq3332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq3417 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (σ x)) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq3310 eq3406
    | exact resolve eq3406 eq3310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3310 eq3406
  have eq3450 : ∀ X0 X1 : G, (M.op (M.op (k X0 X1) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq176 eq185
    | (have j0 := eq185 X0 X1 x
       grind)
    | exact resolve eq185 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq3640 : ∀ X0 X1 : G, (M.op (M.op (k X0 X1) (σ x)) (M.op (σ y) (M.op X0 (σ y)))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1926 eq3450
    | (have j0 := eq3450 X0 X1
       grind)
    | exact resolve eq3450 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3450
  have eq3714 : ∀ X0 X1 : G, (M.op (M.op (k X0 X1) (σ x)) (M.op (σ y) (M.op X0 (σ y)))) = X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3640 X0 X1
       have i₂ := eq655 X0
       grind)
    | exact superpose eq655 eq3640
    | (have j0 := eq3640 X0 X1
       grind)
    | exact resolve eq3640 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3640
  have eq4033 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X2) = (M.op (M.op X1 (M.op (σ y) (σ x))) (M.op X0 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2955 eq177
    | exact resolve eq177 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq4073 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 (σ y))) = (M.op (M.op X1 (M.op X2 X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq2954 eq4033
    | exact resolve eq4033 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954 eq4033
  have eq4144 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq210 eq2846
    | exact resolve eq2846 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq4167 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq2846 eq1759
    | exact resolve eq1759 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4174 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (M.op X0 X2) (M.op (M.op X2 X3) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2846 eq180
    | exact resolve eq180 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4186 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (σ x)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2846 eq1759
    | exact resolve eq1759 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq4224 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2824 eq4144
    | (have j0 := eq4144 (σ y)
       grind)
    | exact resolve eq4144 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq4243 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq4224
       have i₂ := eq655 sF4
       grind)
    | exact superpose eq655 eq4224
    | exact resolve eq4224 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224
  have eq4258 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4243 eq176
    | exact resolve eq176 eq4243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq4243
  have eq4334 : x = (M.op (M.op (M.op x y) (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq194
       have i₂ := eq4167 (M.op sF0 sF0)
       grind)
    | exact superpose eq4167 eq194
    | exact resolve eq194 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq4348 : y = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq1734
       have i₂ := eq4167 sF0
       grind)
    | exact superpose eq4167 eq1734
    | exact resolve eq1734 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4366 : x = (M.op (k (M.op x y) (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq4334
       have i₂ := eq655 sF0
       grind)
    | exact superpose eq655 eq4334
    | exact resolve eq4334 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq4416 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) X0) := by
    intro X0
    first
    | exact superpose eq4348 eq2846
    | exact resolve eq2846 eq4348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4348
  have eq4478 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq4366 eq2846
    | exact resolve eq2846 eq4366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4366
  have eq4532 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op x y)) (M.op y X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2 (M.op y X2)
       have i₂ := eq4416 X2
       grind)
    | exact superpose eq4416 eq177
    | exact resolve eq177 eq4416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4547 : ∀ X0 : G, (M.op y (σ x)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2846 (M.op y sF2) x
       have i₂ := eq4416 sF2
       grind)
    | exact superpose eq4416 eq2846
    | exact resolve eq2846 eq4416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846 eq4416
  have eq4776 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4258 eq1712
    | exact resolve eq1712 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712 eq4258
  have eq4804 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1429 eq4776
    | exact resolve eq4776 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429 eq4776
  have eq4844 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (M.op X0 X1) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1))) := by
    intro X0 X1
    first
    | exact superpose eq4804 eq180
    | exact resolve eq180 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804
  have eq4851 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq4844 x x
       have i₂ := eq4174 sF3 (k sF4 sF4) x x
       grind)
    | exact superpose eq4174 eq4844
    | exact resolve eq4844 eq4174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4844
  have eq5049 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2911 eq1690
    | exact resolve eq1690 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690 eq2911
  have eq5829 : x = (M.op (M.op (M.op x y) (M.op x y)) (k x x)) := by
    first
    | (have i₁ := eq2125
       have i₂ := eq2878 sF0
       grind)
    | exact superpose eq2878 eq2125
    | exact resolve eq2125 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5832 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op (k x x) X0) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq2125 eq180
    | exact resolve eq180 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq5855 : (M.op x y) = (M.op x (M.op (M.op (k x x) (M.op x y)) x)) := by
    first
    | (have i₁ := eq5832 x
       have i₂ := eq224 (k x x) x
       grind)
    | exact superpose eq224 eq5832
    | exact resolve eq5832 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq5832
  have eq5858 : x = (M.op (k (M.op x y) (M.op x y)) (k x x)) := by
    first
    | (have i₁ := eq5829
       have i₂ := eq655 sF0
       grind)
    | exact superpose eq655 eq5829
    | exact resolve eq5829 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5829
  have eq5868 : (M.op x y) = (M.op x (M.op (M.op (k x x) (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq5855
       have i₂ := eq4167 (M.op (k x x) sF0)
       grind)
    | exact superpose eq4167 eq5855
    | exact resolve eq5855 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5855
  have eq5879 : (M.op x y) = (M.op x (M.op y (σ x))) := by
    first
    | exact superpose eq2216 eq5868
    | exact resolve eq5868 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216 eq5868
  have eq5955 : (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq1948 eq3417
    | exact resolve eq3417 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq3417
  have eq5994 : (M.op (k (M.op x y) (M.op x y)) (M.op x y)) = (M.op y (σ x)) := by
    first
    | exact superpose eq4547 eq5955
    | exact resolve eq5955 eq4547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4547 eq5955
  have eq6776 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) X1) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq2095 eq180
    | exact resolve eq180 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq2095
  have eq6795 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq234 eq6776
    | exact resolve eq6776 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq6776
  have eq6816 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ x)) (σ y))) := by
    intro X0
    first
    | exact superpose eq1896 eq6795
    | exact resolve eq6795 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896 eq6795
  have eq6828 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq2074 eq6816
    | exact resolve eq6816 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074 eq6816
  have eq6923 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op X0 (M.op X2 (M.op (σ x) X1))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq2824 eq177
    | exact resolve eq177 eq2824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq6997 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ x) X1) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq6923 X1 X1 x
       have i₂ := eq4073 (M.op sF2 X1) X1 x
       grind)
    | exact superpose eq4073 eq6923
    | exact resolve eq6923 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6923
  have eq7044 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq5049 eq6997
    | exact resolve eq6997 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6997
  have eq7073 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op (σ x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7044 X0 X1
       have i₂ := eq4532 X0 sF3 (M.op sF2 X1)
       grind)
    | exact superpose eq4532 eq7044
    | exact resolve eq7044 eq4532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7044
  have eq7094 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op (σ x) X1))) := by
    intro X0 X1
    first
    | exact superpose eq1926 eq7073
    | exact resolve eq7073 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926 eq7073
  have eq7100 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k (σ y) (σ y))) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op (σ x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7094 X0 X1
       have i₂ := eq655 sF3
       grind)
    | exact superpose eq655 eq7094
    | exact resolve eq7094 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7094
  have eq7101 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op (σ x) X1))) := by
    intro X0 X1
    first
    | exact superpose eq778 eq7100
    | exact resolve eq7100 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq7100
  have eq7573 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (σ x))) := by
    first
    | exact superpose eq5879 eq4478
    | exact resolve eq4478 eq5879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq12584 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 (M.op (σ y) (M.op (M.op (σ x) X2) (σ y)))) X0) (M.op (M.op X0 X1) (M.op X2 X1))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2610 X0 (M.op sF2 X2) X0
       have i₂ := eq177 X0 X1 X2 sF2
       grind)
    | exact superpose eq177 eq2610
    | exact resolve eq2610 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq12607 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op X1 (σ y)))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq2610 eq16
    | exact resolve eq16 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610
  have eq12659 : ∀ X2 X3 : G, (M.op (M.op (M.op X3 (M.op (σ y) (M.op (M.op (σ x) X2) (σ y)))) (σ x)) X2) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq12584 X2 X3 x X3
       have i₂ := eq4174 (M.op X3 (M.op sF3 (M.op (M.op sF2 x) sF3))) x X2 X3
       grind)
    | exact superpose eq4174 eq12584
    | exact resolve eq12584 eq4174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4174 eq12584
  have eq12918 : ∀ X2 X3 : G, (M.op (M.op (M.op X3 (M.op (σ x) (M.op (σ x) X2))) (σ x)) X2) = X3 := by
    intro X2 X3
    first
    | exact superpose eq12607 eq12659
    | exact resolve eq12659 eq12607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12659
  have eq13142 : ∀ X2 X3 : G, (M.op (M.op (M.op X3 (M.op (σ x) (σ y))) (M.op (M.op (σ x) X2) (σ y))) X2) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq12918 X2 x
       have i₂ := eq4073 (M.op sF2 X2) x sF2
       grind)
    | exact superpose eq4073 eq12918
    | exact resolve eq12918 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4073 eq12918
  have eq13341 : ∀ X2 X3 : G, (M.op (M.op (M.op X3 (σ y)) (M.op (M.op (σ x) X2) (σ y))) X2) = X3 := by
    intro X2 X3
    first
    | exact superpose eq5049 eq13142
    | exact resolve eq13142 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049 eq13142
  have eq13504 : ∀ X2 X3 : G, (M.op (M.op (M.op X3 (M.op x y)) (M.op y (M.op (σ x) X2))) X2) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq13341 X2 x
       have i₂ := eq4532 x sF3 (M.op sF2 X2)
       grind)
    | exact superpose eq4532 eq13341
    | exact resolve eq13341 eq4532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4532 eq13341
  have eq13637 : ∀ X2 X3 : G, (M.op (M.op (M.op X3 X2) (σ x)) X2) = X3 := by
    intro X2 X3
    first
    | exact superpose eq7101 eq13504
    | exact resolve eq13504 eq7101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7101 eq13504
  have eq13807 : ∀ X0 : G, (M.op (M.op (k X0 X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13637 X0 X0
       have i₂ := eq655 X0
       grind)
    | exact superpose eq655 eq13637
    | exact resolve eq13637 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13972 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13637 (M.op sF2 X1) (M.op X0 X1)
       have i₂ := eq16 X0 X1 sF2
       grind)
    | exact superpose eq16 eq13637
    | exact resolve eq13637 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13998 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq13637 eq16
    | exact resolve eq16 eq13637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17258 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (k x (M.op x y)) := by
    first
    | (have i₁ := eq5858
       have i₂ := eq1751
       grind)
    | exact superpose eq1751 eq5858
    | exact resolve eq5858 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq17295 : y = (k x (M.op x y)) ∨ x = (M.op y (σ x)) := by
    first
    | exact superpose eq5994 eq17258
    | exact resolve eq17258 eq5994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17258
  have eq18036 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ y) (M.op X2 (σ y)))) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2646 eq13637
    | exact resolve eq13637 eq2646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646 eq13637
  have eq18039 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ y) (M.op X2 (σ y)))) = (M.op (M.op X0 (σ x)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq13972 eq18036
    | exact resolve eq18036 eq13972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18036
  have eq18462 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) (M.op X1 X2)) = (M.op (M.op X0 X1) (M.op (σ x) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq12607 eq18039
    | exact resolve eq18039 eq12607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12607 eq18039
  have eq18878 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (σ x)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq13972 eq18462
    | exact resolve eq18462 eq13972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13972 eq18462
  have eq24070 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y (σ x)) := by
    first
    | exact superpose eq17295 eq42
    | exact resolve eq42 eq17295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17295
  have eq24078 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y (σ x)) := by
    first
    | (have i₁ := eq24070
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24070
    | exact resolve eq24070 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24070
  have eq24083 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y (σ x)) := by
    first
    | (have i₁ := eq24078
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24078
    | exact resolve eq24078 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24078
  have eq26408 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y (σ x)) := by
    first
    | exact superpose eq24083 eq3714
    | (have j0 := eq3714 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq3714 eq24083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3714 eq24083
  have eq26417 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y (σ x)) := by
    first
    | exact superpose eq18878 eq26408
    | exact resolve eq26408 eq18878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18878 eq26408
  have eq26424 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ x)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y (σ x)) := by
    first
    | exact superpose eq1583 eq26417
    | exact resolve eq26417 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq26417
  have eq26430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y (σ x)) := by
    first
    | exact superpose eq4851 eq26424
    | exact resolve eq26424 eq4851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4851 eq26424
  have eq26434 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y (σ x)) := by
    first
    | (have r₁ := eq26430
       have r₂ := eq27
       grind)
    | exact resolve eq26430 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26430
  have eq27055 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op y (σ x)) := by
    first
    | exact superpose eq26434 eq98
    | exact resolve eq98 eq26434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq26434
  have eq27109 : (M.op x y) = (k x x) ∨ x = (M.op y (σ x)) := by
    first
    | exact superpose eq29 eq27055
    | exact resolve eq27055 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27055
  have eq27473 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op y (σ x)) := by
    first
    | (have i₁ := eq5858
       have i₂ := eq27109
       grind)
    | exact superpose eq27109 eq5858
    | exact resolve eq5858 eq27109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858 eq27109
  have eq27520 : x = (M.op y (σ x)) ∨ x = (M.op y (σ x)) := by
    first
    | exact superpose eq5994 eq27473
    | exact resolve eq27473 eq5994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5994 eq27473
  have eq27521 : x = (M.op y (σ x)) := by grind
  clear eq27520
  have eq27549 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq27521 eq7573
    | exact resolve eq7573 eq27521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7573
  have eq27550 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27521 eq5879
    | exact resolve eq5879 eq27521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq27559 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq27521 eq13998
    | exact resolve eq13998 eq27521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13998 eq27521
  have eq27597 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq27559 X0
       have i₂ := eq4167 X0
       grind)
    | exact superpose eq4167 eq27559
    | exact resolve eq27559 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27559
  have eq27604 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq27550
       have i₂ := eq655 x
       grind)
    | exact superpose eq655 eq27550
    | exact resolve eq27550 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq27550
  have eq27605 : y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1734 eq27549
    | exact resolve eq27549 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734 eq27549
  have eq27625 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq27597 X0
       have i₂ := eq2878 X0
       grind)
    | exact superpose eq2878 eq27597
    | exact resolve eq27597 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2878 eq27597
  have eq27815 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq27604
       grind)
    | exact superpose eq27604 eq40
    | exact resolve eq40 eq27604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq27604
  have eq27842 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq27815
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27815
    | exact resolve eq27815 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27815
  have eq27863 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq27842
    | exact resolve eq27842 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27842
  have eq27901 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27605 eq42
    | exact resolve eq42 eq27605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq27605
  have eq27929 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq27901
    | exact resolve eq27901 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq27901
  have eq27949 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq27929
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27929
    | exact resolve eq27929 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq27929
  have eq28099 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27863 eq6828
    | exact resolve eq6828 eq27863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6828 eq27863
  have eq28138 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27625 eq28099
    | exact resolve eq28099 eq27625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28099
  have eq29979 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq27949 eq13807
    | exact resolve eq13807 eq27949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13807 eq27949
  have eq29994 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ x)) (M.op x y)) := by
    first
    | exact superpose eq28138 eq29979
    | exact resolve eq29979 eq28138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28138 eq29979
  have eq30009 : (σ (M.op x y)) = (M.op (M.op (σ y) (M.op x y)) x) := by
    first
    | exact superpose eq4186 eq29994
    | exact resolve eq29994 eq4186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4186 eq29994
  have eq30020 : (σ (M.op x y)) = (M.op (M.op (σ y) (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq30009
       have i₂ := eq4167 (M.op sF3 sF0)
       grind)
    | exact superpose eq4167 eq30009
    | exact resolve eq30009 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4167 eq30009
  have eq30027 : (σ (M.op x y)) = (M.op (M.op (σ y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq27625 eq30020
    | exact resolve eq30020 eq27625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27625 eq30020
  have eq30034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3317 eq30027
    | exact resolve eq30027 eq3317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317 eq30027
  have eq30040 : False := by grind
  exact eq30040

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 X0 y x
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 X0 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq58 eq57
    | exact resolve eq57 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq61 eq117
    | exact resolve eq117 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq125 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
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
  have eq181 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
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
  have eq322 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (M.op (σ x) (σ y)) (σ (k y x))
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq326 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq322
    | exact resolve eq322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq328 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq326
    | exact resolve eq326 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq376 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq54 X0 x X2 X1
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x
       have i₂ := eq54 sF0 x y x
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq58 x
       have i₂ := eq54 sF4 x sF3 x
       grind)
    | exact superpose eq54 eq58
    | exact resolve eq58 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq54 (M.op X0 X1) X2 X1 x
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq376 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq376
    | (have j0 := eq376 X0 x y
       grind)
    | exact resolve eq376 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq376
    | (have j0 := eq376 X0 (σ x) (σ y)
       grind)
    | exact resolve eq376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq376 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) X2 X3
       have i₂ := eq376 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq376 eq376
    | exact resolve eq376 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (σ y))) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq58 eq376
    | exact resolve eq376 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2
       have i₂ := eq376 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq376 eq9
    | exact resolve eq9 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op X0 (M.op y sF0))
       have i₂ := eq376 X0 y sF0
       grind)
    | exact superpose eq376 eq55
    | exact resolve eq55 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 (M.op sF3 sF4))
       have i₂ := eq376 X0 sF3 sF4
       grind)
    | exact superpose eq376 eq57
    | exact resolve eq57 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (M.op X1 y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op X0 (M.op X1 y)) X1)
       have i₂ := eq376 X0 X1 y
       grind)
    | exact superpose eq376 eq55
    | exact resolve eq55 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq473 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op X1 y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 (M.op X1 y)) X1)
       have i₂ := eq376 X0 X1 y
       grind)
    | exact superpose eq376 eq53
    | exact resolve eq53 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq474 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op X1 (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq376 X0 X1 sF3
       grind)
    | exact superpose eq376 eq58
    | exact resolve eq58 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq475 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 (M.op X1 (σ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq376 X0 X1 sF3
       grind)
    | exact superpose eq376 eq57
    | exact resolve eq57 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq475 eq474
    | (have j0 := eq474 X0 (σ x)
       grind)
    | exact resolve eq474 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq479 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq473 X0 x
       have i₂ := eq472 X0 x
       grind)
    | (have i₁ := eq473 X0 x
       have i₂ := eq472 X0 x
       grind)
    | exact superpose eq472 eq473
    | (have j0 := eq473 X0 x
       grind)
    | exact resolve eq473 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq473
  have eq539 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq464 eq376
    | exact resolve eq376 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq574 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq465 eq376
    | exact resolve eq376 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq725 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq382 (M.op X0 (M.op X3 X2)) X3 X4
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq382
    | exact resolve eq382 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq108 eq382
    | exact resolve eq382 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq810 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X4 X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3 X4
       have i₂ := eq382 X0 X1 X2
       grind)
    | exact superpose eq382 eq54
    | exact resolve eq54 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X2 (M.op X0 (M.op X1 X2)) X1 X3
       have i₂ := eq376 X0 X1 X2
       grind)
    | exact superpose eq376 eq56
    | exact resolve eq56 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op (M.op X2 X3) (M.op X1 X3)) (M.op X0 X1) X2 X4
       have i₂ := eq56 X2 X0 X1 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) X0) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq102 eq56
    | exact resolve eq56 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1019 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq56 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 X3)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq376 (M.op (M.op X0 X1) X2) (M.op X2 X3) (M.op X1 X3)
       have i₂ := eq56 X2 X0 X1 X3
       grind)
    | exact superpose eq56 eq376
    | exact resolve eq376 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X5 X4)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) X2) (M.op (M.op X2 X3) (M.op X1 X3)) X4 X5
       have i₂ := eq56 X2 X0 X1 X3
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1033 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1026 X0 X1 X2 X3 X4 x
       have i₂ := eq810 X0 X1 X2 X4 x
       grind)
    | exact superpose eq810 eq1026
    | exact resolve eq1026 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq1026
  have eq1068 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq739 eq935
    | exact resolve eq935 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq935
  have eq1075 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq923 X0 X1 X2 x x
       have i₂ := eq725 X2 x X1 X2 x
       grind)
    | exact superpose eq725 eq923
    | exact resolve eq923 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq923
  have eq1133 : ∀ X0 : G, (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0 (τ X0)
       have i₂ := eq125 (τ X0)
       grind)
    | exact superpose eq125 eq50
    | (have j1 := eq125 (τ X0)
       grind)
    | exact resolve eq50 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq125
  have eq1144 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1133 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1133
    | (have j0 := eq1133 X0
       grind)
    | exact resolve eq1133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1146 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1144 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1144
    | (have j0 := eq1144 X0
       grind)
    | exact resolve eq1144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1148 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1146 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1146 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq1146 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1181 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0 X0
       have i₂ := eq1148 X0
       grind)
    | exact superpose eq1148 eq181
    | exact resolve eq181 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1182 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1148 (σ X0)
       grind)
    | exact superpose eq1148 eq15
    | exact resolve eq15 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1182 X0
       have i₂ := eq1148 X0
       grind)
    | exact superpose eq1148 eq1182
    | exact resolve eq1182 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1184 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1181 X0
       have i₂ := eq1148 (τ X0)
       grind)
    | exact superpose eq1148 eq1181
    | exact resolve eq1181 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq1181
  have eq1195 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1068 eq376
    | exact resolve eq376 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1219 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1195 eq442
    | exact resolve eq442 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq1262 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq1219 eq9
    | exact resolve eq9 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1268 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (σ x))) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1219 eq376
    | exact resolve eq376 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1272 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1268 X0
       have i₂ := eq1021 X0 sF2 sF4 sF2
       grind)
    | exact superpose eq1021 eq1268
    | exact resolve eq1268 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1277 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1262 X0
       have i₂ := eq1021 (M.op X0 sF3) sF2 sF4 sF2
       grind)
    | exact superpose eq1021 eq1262
    | exact resolve eq1262 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq1262
  have eq1322 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1272 (M.op X0 (M.op sF2 sF4))
       have i₂ := eq376 X0 sF2 sF4
       grind)
    | exact superpose eq376 eq1272
    | exact resolve eq1272 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1325 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1272 eq57
    | exact resolve eq57 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1272
  have eq1340 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1325 eq475
    | exact resolve eq475 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq1341 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1325 eq477
    | exact resolve eq477 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq1325
  have eq1378 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1277 (M.op X0 (M.op sF3 sF2))
       have i₂ := eq376 X0 sF3 sF2
       grind)
    | exact superpose eq376 eq1277
    | exact resolve eq1277 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq1569 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (M.op (σ y) (σ x)) X1)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1378 eq54
    | exact resolve eq54 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1669 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 (M.op x (M.op y X1))) := by
    intro X0 X1
    first
    | exact superpose eq380 eq1019
    | exact resolve eq1019 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1670 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq381 eq1019
    | exact resolve eq1019 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1673 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1019 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq382 X0 X2 X3
       grind)
    | exact superpose eq382 eq1019
    | exact resolve eq1019 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1675 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X3 X2))) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1019 X1 (M.op (M.op X0 X2) (M.op X3 X2)) X3
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq1019
    | exact resolve eq1019 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1679 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op X1 (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0 X1
    first
    | exact superpose eq421 eq1019
    | exact resolve eq1019 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq1695 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1019 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq376 X0 X2 X2
       grind)
    | exact superpose eq376 eq1019
    | exact resolve eq1019 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1725 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op X2 X1)
       have i₂ := eq1019 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq1019 eq9
    | exact resolve eq9 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1813 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1679 eq479
    | exact resolve eq479 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq1679
  have eq1827 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq921 X0 X1 X2 x
       have i₂ := eq1675 X2 X0 x X1
       grind)
    | exact superpose eq1675 eq921
    | exact resolve eq921 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq1832 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X4 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X2 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1033 X0 X1 X2 x X4
       have i₂ := eq1675 X2 X4 x X1
       grind)
    | exact superpose eq1675 eq1033
    | exact resolve eq1033 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq1675
  have eq1890 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) X1))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1569 X1 x X2
       have i₂ := eq1673 sF3 X1 sF2 x
       grind)
    | exact superpose eq1673 eq1569
    | exact resolve eq1569 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1947 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1341 X0
       have i₂ := eq1673 X0 (M.op sF4 X0) sF2 sF4
       grind)
    | exact superpose eq1673 eq1341
    | exact resolve eq1341 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1953 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 x
       have i₂ := eq1673 X0 sF4 x sF3
       grind)
    | exact superpose eq1673 eq449
    | exact resolve eq449 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq2077 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1322 eq1947
    | exact resolve eq1947 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq2407 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 (M.op (M.op (σ x) (σ y)) X1))) X2) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2077 eq54
    | exact resolve eq54 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq2416 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2407 X0 x X1
       have i₂ := eq446 X0 X1 sF4 x
       grind)
    | exact superpose eq446 eq2407
    | exact resolve eq2407 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407
  have eq2641 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq381 (M.op sF3 x)
       have i₂ := eq1075 (M.op sF4 (M.op sF3 x)) x sF3
       grind)
    | exact superpose eq1075 eq381
    | exact resolve eq381 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq2852 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2641 eq376
    | exact resolve eq376 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2873 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2852 eq1953
    | exact resolve eq1953 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq3098 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq463 X3 X4 (M.op X0 (M.op X4 X2))
       have i₂ := eq54 X0 X1 X2 X4
       grind)
    | exact superpose eq54 eq463
    | exact resolve eq463 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3102 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) y)) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq539 eq463
    | exact resolve eq463 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq3199 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) y)) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | exact superpose eq1669 eq3102
    | exact resolve eq3102 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq3102
  have eq3203 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3098 X0 X1 X2 X3 X4
       have i₂ := eq1673 X0 X4 X1 (M.op X2 X1)
       grind)
    | exact superpose eq1673 eq3098
    | exact resolve eq3098 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098
  have eq3229 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3199 X0 X1
       have i₂ := eq1673 X0 X1 x y
       grind)
    | exact superpose eq1673 eq3199
    | exact resolve eq3199 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3199
  have eq3232 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3203 X0 x X2 X3 X4
       have i₂ := eq463 X0 x X2
       grind)
    | exact superpose eq463 eq3203
    | exact resolve eq3203 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq3203
  have eq3251 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3229 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3229
    | (have j0 := eq3229 X0 X1
       grind)
    | exact resolve eq3229 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq3255 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ x) (M.op (σ y) X1))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1890 x X2 X2
       have i₂ := eq3232 sF3 X2 x sF2
       grind)
    | (have i₁ := eq1890 x X2 X2
       have i₂ := eq3232 sF2 X2 x sF3
       grind)
    | exact superpose eq3232 eq1890
    | exact resolve eq1890 eq3232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890 eq3232
  have eq3323 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376 X0 X1 (M.op X2 X2)
       have i₂ := eq1695 X1 X0 X2
       grind)
    | exact superpose eq1695 eq376
    | exact resolve eq376 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3324 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X0 X2 (M.op X3 X3) X1
       have i₂ := eq1695 X1 X0 X3
       grind)
    | exact superpose eq1695 eq54
    | exact resolve eq54 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3385 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op X3 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3324 X0 X1 X2 X3
       have i₂ := eq1673 X3 (M.op X0 X2) X3 X2
       grind)
    | exact superpose eq1673 eq3324
    | exact resolve eq3324 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq3416 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3385 X0 X1 X2 x
       have i₂ := eq1075 (M.op X0 X2) X2 x
       grind)
    | exact superpose eq1075 eq3385
    | exact resolve eq3385 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385
  have eq3598 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (σ x)))) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2641 eq96
    | exact resolve eq96 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2641
  have eq3673 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3598 x
       have i₂ := eq446 sF4 sF3 x sF2
       grind)
    | exact superpose eq446 eq3598
    | exact resolve eq3598 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq3598
  have eq4352 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376 (M.op (M.op X0 X2) X1) X1 X2
       have i₂ := eq1725 X0 X2 X1
       grind)
    | exact superpose eq1725 eq376
    | exact resolve eq376 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq4412 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1340 X0 x
       have i₂ := eq4352 X0 (M.op x sF3) x
       grind)
    | (have i₁ := eq1340 X0 X1
       have i₂ := eq4352 X0 X1 (M.op X1 sF3)
       grind)
    | exact superpose eq4352 eq1340
    | exact resolve eq1340 eq4352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq4459 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2416 X0 X1
       have i₂ := eq4352 X0 (M.op X1 sF3) sF2
       grind)
    | (have i₁ := eq2416 X0 X1
       have i₂ := eq4352 X0 sF2 (M.op X1 sF3)
       grind)
    | exact superpose eq4352 eq2416
    | exact resolve eq2416 eq4352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq4466 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3255 X0 X1 X2
       have i₂ := eq4352 X0 (M.op sF2 (M.op sF3 X1)) sF4
       grind)
    | (have i₁ := eq3255 X0 X1 X2
       have i₂ := eq4352 X0 sF4 (M.op sF2 (M.op sF3 X1))
       grind)
    | exact superpose eq4352 eq3255
    | exact resolve eq3255 eq4352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3255 eq4352
  have eq5687 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq574 eq3323
    | exact resolve eq3323 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6825 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X1)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3416 (M.op (M.op X0 X1) X2) X3 (M.op X2 X1)
       have i₂ := eq1725 X0 X1 X2
       grind)
    | exact superpose eq1725 eq3416
    | exact resolve eq3416 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq7275 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq3673 eq3416
    | exact resolve eq3416 eq3673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416 eq3673
  have eq7276 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7275 x x
       have i₂ := eq6825 sF4 x sF2 x
       grind)
    | exact superpose eq6825 eq7275
    | exact resolve eq7275 eq6825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825 eq7275
  have eq7301 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq2852 eq7276
    | exact resolve eq7276 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7276
  have eq10488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq328
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq328
    | (have j1 := eq14 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq328 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq10502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10488
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10488
    | exact resolve eq10488 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10488
  have eq10505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq10502
    | exact resolve eq10502 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502
  have eq10506 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10505
       have r₂ := eq28
       grind)
    | exact resolve eq10505 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10505
  have eq10507 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10506
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10506
    | exact resolve eq10506 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10506
  have eq10509 : (σ y) ≠ (σ y) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10507 eq120
    | (have r₁ := eq120
       have r₂ := eq10507
       grind)
    | exact resolve eq120 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq10512 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10507 eq1195
    | exact resolve eq1195 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10513 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10507 eq1322
    | exact resolve eq1322 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10507
  have eq10528 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10509
  have eq10532 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq10513
    | (have j0 := eq10513 X0
       grind)
    | exact resolve eq10513 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10513
  have eq11273 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10528
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq10528
    | (have j1 := eq14 (σ (M.op x y)) (M.op (σ y) (σ x))
       grind)
    | exact resolve eq10528 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10528
  have eq11289 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq11273
  have eq11292 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11289
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11289
    | exact resolve eq11289 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11289
  have eq11295 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq11292
    | exact resolve eq11292 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11292
  have eq11298 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11295
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11295
    | exact resolve eq11295 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11295
  have eq11299 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11298
  have eq11312 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11299 eq10512
    | exact resolve eq10512 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10512
  have eq11324 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11299 eq1827
    | exact resolve eq1827 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827 eq11299
  have eq11333 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11312
  have eq11336 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq11324
    | (have j0 := eq11324 X0
       grind)
    | exact resolve eq11324 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11324
  have eq11362 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11333 eq3323
    | exact resolve eq3323 eq11333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11333
  have eq11371 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (M.op X0 X0)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2852 eq11362
    | exact resolve eq11362 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11362
  have eq11380 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11371 X0
       have i₂ := eq1075 sF4 (M.op X0 X0) sF3
       grind)
    | exact superpose eq1075 eq11371
    | exact resolve eq11371 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11371
  have eq12002 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10532 eq11380
    | exact resolve eq11380 eq10532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10532 eq11380
  have eq12043 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12002
  have eq12063 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1670 eq12043
    | exact resolve eq12043 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670 eq12043
  have eq12085 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12063
       have i₂ := eq1695 sF2 sF4 sF3
       grind)
    | exact superpose eq1695 eq12063
    | exact resolve eq12063 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12063
  have eq12258 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12085 eq1195
    | exact resolve eq1195 eq12085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq12308 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12258 eq11336
    | exact resolve eq11336 eq12258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11336 eq12258
  have eq12326 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12308
  have eq12358 : (τ (σ x)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12326 eq1184
    | exact resolve eq1184 eq12326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq12326
  have eq12393 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq38 eq12358
    | exact resolve eq12358 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq12358
  have eq12399 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq39 eq12393
    | exact resolve eq12393 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393
  have eq12411 : x = (M.op x (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12399 eq380
    | exact resolve eq380 eq12399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq12399
  have eq12455 : x = (M.op x (M.op x (M.op y y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3251 eq12411
    | exact resolve eq12411 eq3251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251 eq12411
  have eq12472 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12455
       have i₂ := eq1695 x x y
       grind)
    | exact superpose eq1695 eq12455
    | exact resolve eq12455 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12455
  have eq12541 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1183 x
       have i₂ := eq12472
       grind)
    | exact superpose eq12472 eq1183
    | exact resolve eq1183 eq12472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12472
  have eq12582 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12541
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12541
    | exact resolve eq12541 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12541
  have eq12677 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12582 eq574
    | exact resolve eq574 eq12582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq12582
  have eq12717 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2852 eq12677
    | exact resolve eq12677 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12677
  have eq12726 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7301 eq12717
    | exact resolve eq12717 eq7301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7301 eq12717
  have eq12731 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12726
    | exact resolve eq12726 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12726
  have eq12769 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12731 eq3323
    | exact resolve eq3323 eq12731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323 eq12731
  have eq12782 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5687 eq12769
    | exact resolve eq12769 eq5687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5687 eq12769
  have eq12798 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2852 eq12782
    | exact resolve eq12782 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852 eq12782
  have eq12810 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2873 eq12798
    | exact resolve eq12798 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873 eq12798
  have eq12819 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12810
       have i₂ := eq1695 sF2 sF4 sF3
       grind)
    | exact superpose eq1695 eq12810
    | exact resolve eq12810 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695 eq12810
  have eq13019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12819 eq12085
    | exact resolve eq12085 eq12819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12085 eq12819
  have eq13048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13019
  have eq13055 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq13048
       have r₂ := eq28
       grind)
    | exact resolve eq13048 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13048
  have eq13248 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13055 eq40
    | exact resolve eq40 eq13055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq13055
  have eq13265 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39 eq13248
    | exact resolve eq13248 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq13248
  have eq13266 : y = (M.op x y) ∨ x = y := by grind
  clear eq13265
  have eq13270 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13266 eq21
    | exact resolve eq21 eq13266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13279 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op X0 y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13266 eq1813
    | exact resolve eq1813 eq13266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq13266
  have eq13294 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13270
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13270
    | exact resolve eq13270 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13270
  have eq16066 : (σ x) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ x = y := by
    first
    | (have i₁ := eq1183 (M.op y y)
       have i₂ := eq13279 y
       grind)
    | exact superpose eq13279 eq1183
    | exact resolve eq1183 eq13279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13279
  have eq16120 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq16066
       have i₂ := eq1183 y
       grind)
    | exact superpose eq1183 eq16066
    | exact resolve eq16066 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16066
  have eq16164 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ y) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq16120
       have i₂ := eq4466 (σ y) (σ y) (σ y)
       grind)
    | exact superpose eq4466 eq16120
    | exact resolve eq16120 eq4466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466 eq16120
  have eq16194 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (M.op (σ y) (σ y))) (σ y))) ∨ x = y := by
    first
    | exact superpose eq4459 eq16164
    | exact resolve eq16164 eq4459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459 eq16164
  have eq16213 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq16194
       have i₂ := eq1673 sF2 (M.op (σ y) sF2) (M.op sF3 (σ y)) sF3
       grind)
    | exact superpose eq1673 eq16194
    | exact resolve eq16194 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673 eq16194
  have eq16221 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ y))))) ∨ x = y := by
    first
    | (have i₁ := eq16213
       have i₂ := eq1832 (M.op (σ y) sF2) (M.op sF3 (σ y)) sF3 sF2
       grind)
    | (have i₁ := eq16213
       have i₂ := eq1832 (M.op (σ y) sF2) sF3 (M.op sF3 (σ y)) sF2
       grind)
    | exact superpose eq1832 eq16213
    | exact resolve eq16213 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832 eq16213
  have eq16227 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq16221
       have i₂ := eq1075 sF2 (σ y) sF3
       grind)
    | exact superpose eq1075 eq16221
    | exact resolve eq16221 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq16221
  have eq16230 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq16227
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16227
    | exact resolve eq16227 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16227
  have eq16233 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq4412 eq16230
    | exact resolve eq16230 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4412 eq16230
  have eq16235 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq16233
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16233
    | exact resolve eq16233 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16233
  have eq16243 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | exact superpose eq16235 eq382
    | exact resolve eq382 eq16235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq16235
  have eq16284 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1322 eq16243
    | exact resolve eq16243 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq16243
  have eq16299 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq16284
    | exact resolve eq16284 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16284
  have eq16325 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq16299 eq28
    | exact resolve eq28 eq16299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16299
  have eq16386 : x = y := by
    first
    | (have r₁ := eq16325
       have r₂ := eq13294
       grind)
    | exact resolve eq16325 eq13294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13294 eq16325
  have eq16387 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq16386
       grind)
    | exact superpose eq16386 eq19
    | exact resolve eq19 eq16386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq16388 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq16386
       grind)
    | exact superpose eq16386 eq25
    | exact resolve eq25 eq16386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16386
  have eq17052 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16388
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16388
    | exact resolve eq16388 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16388
  have eq17114 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17052 eq27
    | exact resolve eq27 eq17052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17052
  have eq17611 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1183 x
       have i₂ := eq16387
       grind)
    | exact superpose eq16387 eq1183
    | exact resolve eq1183 eq16387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq16387
  have eq17681 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17611
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17611
    | exact resolve eq17611 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17611
  have eq17806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17114 eq17681
    | exact resolve eq17681 eq17114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17114 eq17681
  have eq17916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq17806
    | exact resolve eq17806 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17806
  have eq18013 : False := by grind
  exact eq18013

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pxx_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq76 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq80 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq80
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq96
  have eq103 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq124 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq126
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq126
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq143
  have eq203 : x = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 X1) (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op y X1))
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : x = (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op y y))) := by
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) (M.op (M.op x y) (M.op X1 y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x (M.op X1 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 X1) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op sF3 X1))
       have i₂ := eq14 X0 X1 sF3
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) (M.op (M.op x y) (M.op (σ y) y))) := by
    first
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (M.op X1 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op X0 (M.op X1 x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : (M.op (M.op x y) (M.op (σ y) y)) = (M.op (M.op x (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq50 eq54
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 X2 : G, (M.op x (M.op X1 X0)) = (M.op (M.op (M.op (M.op x y) (M.op X0 y)) (M.op X2 X1)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 (M.op X2 (M.op (M.op x y) (M.op X1 y)))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X3 X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 X4) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 X2 X3 (M.op (M.op X0 X4) (M.op X3 X4))
       have i₂ := eq14 X0 X4 X3
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4) (M.op X3 X4)) = (M.op X0 X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4 X3 X2
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (σ y))) X2) (M.op X1 X2)) = (M.op (σ x) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) X2 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 X3) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 x
       have i₂ := eq52 X0 X3 X2 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 x X2
       have i₂ := eq52 X0 x X2 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op X3 (M.op X0 X2)) = (k X3 (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X0 X2)
       have i₂ := eq52 X0 X2 X0 X1
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 X3 (M.op X0 X2)
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) (M.op X0 X4)) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X3 (M.op X2 X4) (M.op X0 X4)
       have i₂ := eq52 X0 X4 X2 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X4 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X2 X3) X4
       have i₂ := eq52 X0 X3 X2 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op x y)) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 (M.op y X2))
       have i₂ := eq52 X0 X1 X2 y
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x X1) (M.op (M.op X1 X2) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X2 X3) (M.op X1 X3)) (M.op X0 X1) X2 X4
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) (M.op (M.op X2 X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 (M.op X0 X1) (M.op X2 X1) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x X1) (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) X1) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op x y) (M.op X2 y))) (M.op x (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) (M.op (σ x) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X4) (M.op X0 (M.op X5 X2))) (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X4 X5))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X0 (M.op X5 X2)) X3 X4 X5
       have i₂ := eq52 X0 X1 X2 X5
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X0 (M.op X4 X2))) X5) (M.op (M.op X5 X4) (M.op (M.op X0 X1) (M.op X2 X1)))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X5 X3 (M.op X0 (M.op X4 X2)) X4
       have i₂ := eq52 X0 X1 X2 X4
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) X2) (M.op (M.op X2 (σ x)) X0)) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X2) X0) (M.op (M.op X0 (M.op X1 X2)) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X3 X2 x
       have i₂ := eq52 X0 x X2 X1
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq55 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X5 (M.op (M.op X0 X4) X2))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X1 (M.op (M.op X2 X3) (M.op X4 X3)) (M.op (M.op X0 X4) X2) X5
       have i₂ := eq55 X2 X0 X4 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq574 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) X2) (M.op (M.op X2 X3) (M.op (σ X0) X3))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 (σ X1) (σ X0) X3
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq55
    | (have j1 := eq74 X0 X0
       grind)
    | exact resolve eq55 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq847 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (M.op x y) (M.op (σ y) y))) (M.op x (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq227 eq14
    | exact resolve eq14 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq866 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq386
    | exact resolve eq386 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op (M.op X2 X3) (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq386 (M.op X0 X1) X2 (M.op (M.op X2 X3) (M.op X1 X3))
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq386
    | exact resolve eq386 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq386 (M.op X0 X1) X2 (M.op X1 X2)
       have i₂ := eq386 X0 X1 X2
       grind)
    | exact superpose eq386 eq386
    | exact resolve eq386 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq386
    | exact resolve eq386 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq53 eq386
    | exact resolve eq386 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : (M.op x y) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq203 eq386
    | exact resolve eq386 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq54 eq386
    | exact resolve eq386 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq386
    | (have j0 := eq386 X0 (σ x) (σ y)
       grind)
    | exact resolve eq386 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 (M.op X0 (M.op X1 X2)) X1 X3
       have i₂ := eq390 X0 X1 X2
       grind)
    | exact superpose eq390 eq55
    | exact resolve eq55 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1160 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq388 eq484
    | exact resolve eq484 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1164 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq484 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq386 X0 X2 X3
       grind)
    | exact superpose eq386 eq484
    | exact resolve eq484 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1166 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) (M.op X1 y))) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq484
    | exact resolve eq484 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq484
    | exact resolve eq484 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | exact superpose eq203 eq484
    | exact resolve eq484 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1180 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq210 eq484
    | exact resolve eq484 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq484 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq484
    | (have j0 := eq484 X0 x y
       grind)
    | exact resolve eq484 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq484
    | (have j0 := eq484 X0 (σ x) (σ y)
       grind)
    | exact resolve eq484 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq390 X0 X2 X2
       grind)
    | exact superpose eq390 eq484
    | exact resolve eq484 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484 (M.op (M.op X0 (M.op X1 X2)) X2) X1 X2
       have i₂ := eq386 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq386 eq484
    | exact resolve eq484 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1219 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X1)
       have i₂ := eq484 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq484 eq14
    | exact resolve eq14 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op x y)
       have i₂ := eq484 sF0 x y
       grind)
    | exact superpose eq484 eq50
    | exact resolve eq50 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1375 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ x) (M.op y (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq388 eq204
    | exact resolve eq204 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1572 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) (M.op (M.op (M.op X0 X1) (M.op y X1)) y))) := by
    intro X0 X1
    first
    | exact superpose eq204 eq206
    | exact resolve eq206 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1581 : (M.op (M.op x y) x) = (M.op (M.op x x) (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op y y)) y))) := by
    first
    | exact superpose eq205 eq206
    | exact resolve eq206 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq206
  have eq1648 : (M.op (M.op x y) x) = (M.op (M.op x x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq50 eq1581
    | exact resolve eq1581 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1649 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1572 X0 x
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq1572
    | exact resolve eq1572 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq1650 : (M.op (M.op x y) x) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq894 eq1648
    | exact resolve eq1648 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1721 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) y) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1182 (M.op (M.op X0 sF0) y)
       have i₂ := eq386 X0 sF0 y
       grind)
    | exact superpose eq386 eq1182
    | exact resolve eq1182 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq2009 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1186 eq51
    | exact resolve eq51 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2165 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2009 eq484
    | exact resolve eq484 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2166 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq900 eq2165
    | exact resolve eq2165 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq2223 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) (σ y)))) := by
    first
    | exact superpose eq213 eq214
    | exact resolve eq214 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq214
  have eq2296 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq51 eq2223
    | exact resolve eq2223 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq2303 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq900 eq2296
    | exact resolve eq2296 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq2326 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x X0) y) := by
    intro X0
    first
    | exact superpose eq1234 eq390
    | exact resolve eq390 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq2505 : ∀ X0 : G, (M.op (σ x) (M.op y X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq215 eq53
    | exact resolve eq53 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2554 : x = (M.op (M.op (M.op x y) (M.op (M.op x y) x)) (M.op x x)) := by
    first
    | (have i₁ := eq50 (M.op x x)
       have i₂ := eq1650
       grind)
    | exact superpose eq1650 eq50
    | exact resolve eq50 eq1650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1650
  have eq2578 : x = (M.op (M.op (M.op x y) y) (M.op x x)) := by
    first
    | exact superpose eq894 eq2554
    | exact resolve eq2554 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq2925 : ∀ X0 : G, (M.op X0 (M.op (σ y) x)) = (M.op (M.op (M.op (M.op X0 y) (M.op x y)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 (M.op sF3 x))
       have i₂ := eq224 X0 sF3
       grind)
    | exact superpose eq224 eq54
    | exact resolve eq54 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq224
  have eq3093 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | exact superpose eq1721 eq386
    | exact resolve eq386 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721
  have eq3783 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq2578 eq390
    | exact resolve eq390 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq10185 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ x) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1) (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq210 eq442
    | exact resolve eq442 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq10694 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10185 X0 X1
       have i₂ := eq887 X0 (M.op (M.op sF4 sF4) X1) sF2
       grind)
    | exact superpose eq887 eq10185
    | exact resolve eq10185 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10185
  have eq11237 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) X2 (M.op X2 (M.op X2 X1))
       have i₂ := eq480 X2 X2 X1 X0
       grind)
    | exact superpose eq480 eq14
    | exact resolve eq14 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11239 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq889 (M.op (M.op y (M.op X0 X0)) X0)
       have i₂ := eq480 y X0 X0 (M.op y (M.op X0 X0))
       grind)
    | exact superpose eq480 eq889
    | exact resolve eq889 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq889
  have eq14341 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) x)) = (M.op (M.op X0 (σ y)) x) := by
    intro X0
    first
    | exact superpose eq212 eq366
    | exact resolve eq366 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq14711 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq390 X0 X1 (M.op X2 X2)
       have i₂ := eq1190 X1 X0 X2
       grind)
    | exact superpose eq1190 eq390
    | exact resolve eq390 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15150 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1195 (M.op (M.op X0 X2) X1) X2 X1
       have i₂ := eq386 X0 X2 X1
       grind)
    | exact superpose eq386 eq1195
    | exact resolve eq1195 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq16570 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq203 eq1219
    | exact resolve eq1219 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq18269 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq211 X0 x
       have i₂ := eq375 X0 x sF3
       grind)
    | exact superpose eq375 eq211
    | exact resolve eq211 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq18449 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq18269 X0
       have i₂ := eq1190 sF4 (M.op X0 sF2) sF3
       grind)
    | exact superpose eq1190 eq18269
    | exact resolve eq18269 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18269
  have eq18661 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1649 x
       have i₂ := eq389 x x sF0 x
       grind)
    | (have i₁ := eq1649 x
       have i₂ := eq389 x x sF0 x
       grind)
    | exact superpose eq389 eq1649
    | exact resolve eq1649 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq1649
  have eq21637 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (σ y)))) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq384 eq211
    | exact resolve eq211 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq384
  have eq21753 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq21637 x
       have i₂ := eq484 sF4 x sF3
       grind)
    | exact superpose eq484 eq21637
    | exact resolve eq21637 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21637
  have eq22509 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x X1))) = (M.op (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) y) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq447 eq400
    | exact resolve eq400 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq447
  have eq22631 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 (M.op y (M.op x X1))) := by
    intro X0 X1
    first
    | exact superpose eq53 eq22509
    | exact resolve eq22509 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22509
  have eq26246 : (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) y)) = (M.op (M.op x (σ x)) (σ y)) := by
    first
    | exact superpose eq449 eq431
    | exact resolve eq431 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq31510 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op x y) (M.op x y))) (M.op x (M.op X1 x))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq457
    | (have j0 := eq457 X0 X1 x
       grind)
    | exact resolve eq457 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq31990 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op x y) (M.op x y))) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31510 X0 X1
       have i₂ := eq887 (M.op (M.op X0 X1) (M.op sF0 sF0)) X1 x
       grind)
    | exact superpose eq887 eq31510
    | exact resolve eq31510 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31510
  have eq32078 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op x x)) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1173 eq31990
    | exact resolve eq31990 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173 eq31990
  have eq33034 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq51 eq458
    | exact resolve eq458 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq458
  have eq33551 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33034 X0 X1
       have i₂ := eq1190 sF4 X1 sF3
       grind)
    | exact superpose eq1190 eq33034
    | exact resolve eq33034 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq33034
  have eq33645 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ y)) (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq900 eq33551
    | exact resolve eq33551 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq33551
  have eq43109 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq21753 eq1195
    | exact resolve eq1195 eq21753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq21753
  have eq45544 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op X2 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq210 eq373
    | exact resolve eq373 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq45894 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq449 eq373
    | exact resolve eq373 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq449
  have eq46502 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45544 X0 X1 X1
       have i₂ := eq887 (M.op X0 (M.op sF4 sF4)) X1 sF2
       grind)
    | exact superpose eq887 eq45544
    | exact resolve eq45544 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45544
  have eq46813 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op (σ x) (σ x))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1180 eq46502
    | exact resolve eq46502 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46502
  have eq56572 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq477 eq441
    | exact resolve eq441 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq56577 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq441 X2 (M.op X0 X1) X1 x x
       have i₂ := eq382 X1 x X0 X1 x
       grind)
    | exact superpose eq382 eq441
    | exact resolve eq441 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq56606 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op (M.op y X0) (M.op X1 X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq204 eq441
    | exact resolve eq441 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq441
  have eq65364 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75
    | (have j0 := eq75 x
       grind)
    | exact resolve eq75 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq65482 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq65364
  have eq65511 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65482
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq65482
    | exact resolve eq65482 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65482
  have eq65525 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq65511
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq65511 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65511
  have eq65530 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq65525 eq49
    | exact resolve eq49 eq65525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq65589 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq76 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq76
    | (have j0 := eq76 y
       grind)
    | exact resolve eq76 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq65711 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq65589
  have eq65734 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq65711
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq65711
    | exact resolve eq65711 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65711
  have eq65751 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq65734
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq65734 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65734
  have eq65760 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq65751 eq101
    | exact resolve eq101 eq65751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq66175 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq127
    | (have j0 := eq127 (M.op x y)
       grind)
    | exact resolve eq127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq66276 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq66175
  have eq66283 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq126 eq66276
    | exact resolve eq66276 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66276
  have eq66294 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq66283
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq66283 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66283
  have eq66304 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq66294 eq149
    | exact resolve eq149 eq66294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq110247 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) (M.op X3 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq393 (M.op X2 X2) (M.op X1 X3) X2 (M.op X0 X1) (M.op X3 (M.op X1 X3))
       have i₂ := eq459 X2 X2 (M.op X1 X3) X0 X1 X3
       grind)
    | exact superpose eq459 eq393
    | exact resolve eq393 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq459
  have eq110549 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110247 X0 X1 X2 x
       have i₂ := eq887 (M.op X2 X2) X1 x
       grind)
    | exact superpose eq887 eq110247
    | exact resolve eq110247 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110247
  have eq112744 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (M.op (M.op X1 X1) X0) (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18449 (M.op (M.op x x) X1)
       have i₂ := eq110549 sF4 X1 x
       grind)
    | exact superpose eq110549 eq18449
    | exact resolve eq18449 eq110549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18449
  have eq112755 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X1 X1) X0) (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq112744 X0 X1
       have i₂ := eq56577 (M.op (M.op (M.op X1 X1) X0) sF2) sF4 (M.op sF4 X0)
       grind)
    | (have i₁ := eq112744 X0 X1
       have i₂ := eq56577 sF4 (M.op (M.op (M.op X1 X1) X0) sF2) (M.op sF4 X0)
       grind)
    | exact superpose eq56577 eq112744
    | exact resolve eq112744 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112744
  have eq113182 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq112755 X0 X1
       have i₂ := eq56577 (M.op (M.op X1 X1) X0) sF2 sF4
       grind)
    | (have i₁ := eq112755 X0 X1
       have i₂ := eq56577 sF2 (M.op (M.op X1 X1) X0) sF4
       grind)
    | exact superpose eq56577 eq112755
    | exact resolve eq112755 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112755
  have eq113300 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq113182 x x
       have i₂ := eq110549 sF2 x x
       grind)
    | exact superpose eq110549 eq113182
    | exact resolve eq113182 eq110549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110549 eq113182
  have eq119140 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq394 X0 X1 (M.op X1 X2) (M.op X2 X2) (M.op X1 X1)
       have i₂ := eq473 X1 X2 X2 X0 X1 X1
       grind)
    | exact superpose eq473 eq394
    | exact resolve eq394 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq473
  have eq130458 : ∀ X0 X2 X3 : G, (M.op (M.op X0 x) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op X2 y) (M.op x y)))) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq387 eq491
    | exact resolve eq491 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq130461 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (σ x)) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op X2 (σ y)) (M.op (σ x) (σ y))))) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq388 eq491
    | exact resolve eq491 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq491
  have eq133801 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (σ x)) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y))))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq130461 X0 X2 X2
       have i₂ := eq56577 (M.op X2 sF3) sF4 X2
       grind)
    | (have i₁ := eq130461 X0 X2 X2
       have i₂ := eq56577 sF4 (M.op X2 sF3) X2
       grind)
    | exact superpose eq56577 eq130461
    | exact resolve eq130461 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130461
  have eq133804 : ∀ X0 X2 X3 : G, (M.op (M.op X0 x) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op x y) (M.op X2 y)))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq130458 X0 X2 X2
       have i₂ := eq56577 (M.op X2 y) sF0 X2
       grind)
    | (have i₁ := eq130458 X0 X2 X2
       have i₂ := eq56577 sF0 (M.op X2 y) X2
       grind)
    | exact superpose eq56577 eq130458
    | exact resolve eq130458 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130458
  have eq134701 : ∀ X0 X2 : G, (M.op (M.op X0 X2) (σ x)) = (M.op (M.op X0 (σ x)) X2) := by
    intro X0 X2
    first
    | exact superpose eq367 eq133801
    | exact resolve eq133801 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq133801
  have eq134704 : ∀ X0 X2 : G, (M.op (M.op X0 X2) x) = (M.op (M.op X0 x) X2) := by
    intro X0 X2
    first
    | exact superpose eq366 eq133804
    | exact resolve eq133804 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq133804
  have eq204112 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq65525 eq87
    | exact resolve eq87 eq65525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq205020 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq65751 eq102
    | exact resolve eq102 eq65751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq213427 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq66294 eq150
    | exact resolve eq150 eq66294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq221060 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq927 eq866
    | exact resolve eq866 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq221995 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq221060 X0
       have i₂ := eq484 sF4 (M.op X0 sF2) sF3
       grind)
    | exact superpose eq484 eq221060
    | exact resolve eq221060 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221060
  have eq297820 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) x)) = (M.op (M.op X0 x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14341 X0
       have i₂ := eq134704 X0 sF3
       grind)
    | exact superpose eq134704 eq14341
    | exact resolve eq14341 eq134704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14341
  have eq297821 : ∀ X0 : G, (M.op (M.op X0 x) (σ y)) = (M.op (M.op X0 (σ x)) (M.op x (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq297820 X0
       have i₂ := eq56577 sF4 x (M.op X0 sF2)
       grind)
    | (have i₁ := eq297820 X0
       have i₂ := eq56577 x sF4 (M.op X0 sF2)
       grind)
    | exact superpose eq56577 eq297820
    | exact resolve eq297820 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297820
  have eq391881 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56572 X0 x
       have i₂ := eq56577 (M.op X0 sF2) sF4 x
       grind)
    | (have i₁ := eq56572 X0 x
       have i₂ := eq56577 sF4 (M.op X0 sF2) x
       grind)
    | exact superpose eq56577 eq56572
    | exact resolve eq56572 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56572
  have eq391882 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X1) (M.op (M.op y X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56606 X0 x
       have i₂ := eq15150 sF0 (M.op (M.op y X0) (M.op x X0)) x
       grind)
    | (have i₁ := eq56606 X0 X1
       have i₂ := eq15150 sF0 X1 (M.op (M.op y X0) (M.op X1 X0))
       grind)
    | exact superpose eq15150 eq56606
    | exact resolve eq56606 eq15150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56606
  have eq461993 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq204112
       grind)
    | exact superpose eq204112 eq16
    | exact resolve eq16 eq204112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204112
  have eq462080 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq65530 eq461993
    | exact resolve eq461993 eq65530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461993
  have eq462109 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq462080
       have r₂ := eq13 x x
       grind)
    | exact resolve eq462080 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462080
  have eq462136 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq462109
       grind)
    | exact superpose eq462109 eq43
    | exact resolve eq43 eq462109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq462173 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq65525 eq462136
    | exact resolve eq462136 eq65525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65525 eq462136
  have eq462618 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq205020
       grind)
    | exact superpose eq205020 eq16
    | exact resolve eq16 eq205020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205020
  have eq462709 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq65760 eq462618
    | exact resolve eq462618 eq65760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462618
  have eq462738 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq462709
       have r₂ := eq13 x y
       grind)
    | exact resolve eq462709 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462709
  have eq462758 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq462738
       grind)
    | exact superpose eq462738 eq72
    | exact resolve eq72 eq462738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq462795 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq65751 eq462758
    | exact resolve eq462758 eq65751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65751 eq462758
  have eq463247 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq213427 eq16
    | exact resolve eq16 eq213427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213427
  have eq463327 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq66304 eq463247
    | exact resolve eq463247 eq66304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66304 eq463247
  have eq463335 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq463327
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq463327 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463327
  have eq463336 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq463335 eq126
    | exact resolve eq126 eq463335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq463335
  have eq463373 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq66294 eq463336
    | exact resolve eq463336 eq66294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66294 eq463336
  have eq539155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq539169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq539155
    | exact resolve eq539155 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539155
  have eq539176 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq539169
       have r₂ := eq27
       grind)
    | exact resolve eq539169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539169
  have eq539183 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq539176 eq65760
    | exact resolve eq65760 eq539176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539176
  have eq539683 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq539183
       have i₂ := eq462738
       grind)
    | exact superpose eq462738 eq539183
    | exact resolve eq539183 eq462738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539183
  have eq539814 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq539683
    | exact resolve eq539683 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539683
  have eq539815 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq539814
  have eq539953 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq539815 eq65530
    | exact resolve eq65530 eq539815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65530 eq539815
  have eq540485 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq539953
       have i₂ := eq462109
       grind)
    | exact superpose eq462109 eq539953
    | exact resolve eq539953 eq462109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462109 eq539953
  have eq540629 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq540485
    | exact resolve eq540485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540485
  have eq540630 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq540629
  have eq540729 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq462795
       have i₂ := eq540630
       grind)
    | exact superpose eq540630 eq462795
    | exact resolve eq462795 eq540630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540787 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq540630
       grind)
    | exact superpose eq540630 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq540630
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq540630
       grind)
    | exact resolve eq13 eq540630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540630
  have eq541010 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq540787 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540787
  have eq541203 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq540729
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq540729
    | exact resolve eq540729 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540729
  have eq541461 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq541203 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq541203
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq541203
       grind)
    | exact resolve eq13 eq541203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541203
  have eq541686 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq541461 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541461
  have eq546788 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq541010 x
       grind)
    | exact superpose eq541010 eq44
    | exact resolve eq44 eq541010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq541010
  have eq546872 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq546788
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq546788
    | exact resolve eq546788 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546788
  have eq546895 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq546872
    | exact resolve eq546872 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546872
  have eq561953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq541686 eq546895
    | exact resolve eq546895 eq541686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541686 eq546895
  have eq561992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq561953
  have eq562014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq561992
    | exact resolve eq561992 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561992
  have eq562018 : x = (M.op x x) := by
    first
    | (have r₁ := eq562014
       have r₂ := eq27
       grind)
    | exact resolve eq562014 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562014
  have eq562039 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq462173
       have i₂ := eq562018
       grind)
    | exact superpose eq562018 eq462173
    | exact resolve eq462173 eq562018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562055 : (M.op (M.op x y) x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq18661 x
       have i₂ := eq562018
       grind)
    | exact superpose eq562018 eq18661
    | exact resolve eq18661 eq562018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18661
  have eq562282 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1219 x x X0
       have i₂ := eq562018
       grind)
    | exact superpose eq562018 eq1219
    | exact resolve eq1219 eq562018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq562299 : x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq32078 x x
       have i₂ := eq562018
       grind)
    | exact superpose eq562018 eq32078
    | exact resolve eq32078 eq562018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562356 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq562299
       have i₂ := eq3783
       grind)
    | exact superpose eq3783 eq562299
    | exact resolve eq562299 eq3783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3783 eq562299
  have eq562371 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq562282 x
       have i₂ := eq16570 x
       grind)
    | exact superpose eq16570 eq562282
    | exact resolve eq562282 eq16570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16570 eq562282
  have eq562558 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq896 eq562055
    | exact resolve eq562055 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq562055
  have eq562571 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq562039
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq562039
    | exact resolve eq562039 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562039
  have eq563520 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq562371 eq463373
    | exact resolve eq463373 eq562371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463373
  have eq564046 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq563520
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq563520
    | exact resolve eq563520 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563520
  have eq568507 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op x (M.op (σ x) (σ y)))) (M.op (M.op x y) (M.op (σ y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq847 X0
       have i₂ := eq15150 (M.op X0 sF2) (M.op sF0 (M.op sF3 y)) (M.op x sF4)
       grind)
    | (have i₁ := eq847 X0
       have i₂ := eq15150 (M.op X0 sF2) (M.op x sF4) (M.op sF0 (M.op sF3 y))
       grind)
    | exact superpose eq15150 eq847
    | exact resolve eq847 eq15150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq568508 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op x (M.op (σ x) (σ y)))) (M.op x (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq1166 eq568507
    | exact resolve eq568507 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568507
  have eq568509 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op x (σ y))) (M.op x (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq568508 X0
       have i₂ := eq15150 (M.op X0 sF2) (M.op x sF4) (M.op x sF3)
       grind)
    | (have i₁ := eq568508 X0
       have i₂ := eq15150 (M.op X0 sF2) (M.op x sF3) (M.op x sF4)
       grind)
    | exact superpose eq15150 eq568508
    | exact resolve eq568508 eq15150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568508
  have eq568589 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op x (σ y))) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq221995 eq568509
    | exact resolve eq568509 eq221995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221995 eq568509
  have eq569045 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (σ y))) (M.op (σ x) (σ x))) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq568589
       have i₂ := eq15150 sF4 (M.op sF2 sF2) (M.op x sF3)
       grind)
    | (have i₁ := eq568589
       have i₂ := eq15150 sF4 (M.op x sF3) (M.op sF2 sF2)
       grind)
    | exact superpose eq15150 eq568589
    | exact resolve eq568589 eq15150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568589
  have eq569181 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (σ y))) (M.op x (M.op (σ x) (σ y)))) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq569045
       have i₂ := eq15150 (M.op sF4 (M.op x sF3)) (M.op sF2 sF2) (M.op x sF4)
       grind)
    | (have i₁ := eq569045
       have i₂ := eq15150 (M.op sF4 (M.op x sF3)) (M.op x sF4) (M.op sF2 sF2)
       grind)
    | exact superpose eq15150 eq569045
    | exact resolve eq569045 eq15150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569045
  have eq569264 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (σ y))) (M.op x (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq562571 eq569181
    | exact resolve eq569181 eq562571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569181
  have eq569316 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (σ y))) (σ x)) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq134701 eq569264
    | exact resolve eq569264 eq134701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569264
  have eq569351 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (σ y))) x) (σ y)) := by
    first
    | exact superpose eq297821 eq569316
    | exact resolve eq569316 eq297821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297821 eq569316
  have eq569375 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq569351
       have i₂ := eq390 sF4 x sF3
       grind)
    | exact superpose eq390 eq569351
    | exact resolve eq569351 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq569351
  have eq569405 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq569375 eq2166
    | exact resolve eq2166 eq569375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166
  have eq569630 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq569375 eq32078
    | exact resolve eq32078 eq569375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32078
  have eq569635 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq569375 eq45894
    | exact resolve eq45894 eq569375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45894
  have eq569661 : x = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op y (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq569375 eq391882
    | exact resolve eq391882 eq569375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391882 eq569375
  have eq569664 : x = (M.op (M.op (M.op x y) (σ x)) y) := by
    first
    | (have i₁ := eq569661
       have i₂ := eq484 (M.op sF0 sF2) y sF4
       grind)
    | exact superpose eq484 eq569661
    | exact resolve eq569661 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq569661
  have eq569686 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1180 eq569635
    | exact resolve eq569635 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569635
  have eq569691 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op x x)) := by
    first
    | (have i₁ := eq569630
       have i₂ := eq15150 sF4 (M.op x x) sF4
       grind)
    | (have i₁ := eq569630
       have i₂ := eq15150 sF4 sF4 (M.op x x)
       grind)
    | exact superpose eq15150 eq569630
    | exact resolve eq569630 eq15150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569630
  have eq569891 : x = (M.op (M.op (M.op x y) y) (σ x)) := by
    first
    | (have i₁ := eq569664
       have i₂ := eq15150 sF0 sF2 y
       grind)
    | (have i₁ := eq569664
       have i₂ := eq15150 sF0 y sF2
       grind)
    | exact superpose eq15150 eq569664
    | exact resolve eq569664 eq15150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569664
  have eq569903 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq562571 eq569686
    | exact resolve eq569686 eq562571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569686
  have eq569907 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) x) := by
    first
    | (have i₁ := eq569691
       have i₂ := eq562018
       grind)
    | exact superpose eq562018 eq569691
    | exact resolve eq569691 eq562018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569691
  have eq570020 : x = (M.op x (σ x)) := by
    first
    | exact superpose eq562356 eq569891
    | exact resolve eq569891 eq562356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569891
  have eq570023 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq569903
    | exact resolve eq569903 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569903
  have eq570025 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq569907
       have i₂ := eq134704 sF4 sF4
       grind)
    | exact superpose eq134704 eq569907
    | exact resolve eq569907 eq134704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569907
  have eq570388 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | exact superpose eq570020 eq11237
    | exact resolve eq11237 eq570020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570458 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq570388 X0
       have i₂ := eq562018
       grind)
    | exact superpose eq562018 eq570388
    | exact resolve eq570388 eq562018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562018 eq570388
  have eq570988 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq570023 eq2009
    | exact resolve eq2009 eq570023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009
  have eq581379 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10694 X0 (M.op (M.op (M.op sF4 sF4) x) (M.op X1 x))
       have i₂ := eq886 X0 X1 (M.op sF4 sF4) x
       grind)
    | exact superpose eq886 eq10694
    | exact resolve eq10694 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq10694
  have eq583023 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (σ x) X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq570988 eq581379
    | exact resolve eq581379 eq570988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581379
  have eq584589 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq866 eq583023
    | (have j0 := eq583023 X0 X1 (σ y)
       grind)
    | exact resolve eq583023 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq583023
  have eq585411 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1167 eq584589
    | exact resolve eq584589 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq584589
  have eq634645 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) (σ y)) := by
    first
    | exact superpose eq569405 eq570025
    | exact resolve eq570025 eq569405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570025
  have eq638562 : (M.op x (σ x)) = (M.op x (M.op (M.op y (M.op (σ y) y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1375 eq361
    | exact resolve eq361 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq1375
  have eq639160 : (M.op x (σ x)) = (M.op x (M.op y (M.op (M.op (σ y) y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq638562
       have i₂ := eq1164 y x (M.op sF3 y) sF4
       grind)
    | exact superpose eq1164 eq638562
    | exact resolve eq638562 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638562
  have eq639582 : (M.op x (σ x)) = (M.op x (M.op y (M.op (σ y) (M.op y (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq639160
       have i₂ := eq1164 sF3 y y sF4
       grind)
    | exact superpose eq1164 eq639160
    | exact resolve eq639160 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164 eq639160
  have eq639910 : (M.op x (σ x)) = (M.op x (M.op y (M.op (σ y) (M.op y (σ y))))) := by
    first
    | exact superpose eq569405 eq639582
    | exact resolve eq639582 eq569405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639582
  have eq640170 : (M.op x (σ x)) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq639910
       have i₂ := eq887 y y sF3
       grind)
    | exact superpose eq887 eq639910
    | exact resolve eq639910 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq639910
  have eq640366 : x = (M.op x (M.op y y)) := by
    first
    | exact superpose eq570020 eq640170
    | exact resolve eq640170 eq570020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570020 eq640170
  have eq640604 : ∀ X0 : G, x = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq640366
       have i₂ := eq119140 x X0 y
       grind)
    | (have i₁ := eq640366
       have i₂ := eq119140 x y X0
       grind)
    | exact superpose eq119140 eq640366
    | exact resolve eq640366 eq119140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641984 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2326 (M.op X0 X0)
       have i₂ := eq640604 X0
       grind)
    | exact superpose eq640604 eq2326
    | exact resolve eq2326 eq640604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2326
  have eq642172 : ∀ X1 X2 : G, x ≠ (M.op (M.op x (M.op X1 x)) X1) ∨ (M.op X2 x) = (k X2 x) := by
    intro X1 X2
    first
    | (have i₁ := eq392 x X1 (M.op x x) x
       have i₂ := eq640604 x
       grind)
    | exact superpose eq640604 eq392
    | exact resolve eq392 eq640604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640604
  have eq642502 : ∀ X2 : G, x ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op X2 x) = (k X2 x) := by
    intro X2
    first
    | (have i₁ := eq642172 x X2
       have i₂ := eq207 x x
       grind)
    | exact superpose eq207 eq642172
    | (have j0 := eq642172 x X2
       grind)
    | exact resolve eq642172 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq642172
  have eq642661 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq641984 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq641984
    | (have j0 := eq641984 X0
       grind)
    | exact resolve eq641984 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641984
  have eq642926 : ∀ X2 : G, x ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op X2 x) = (k X2 x) := by
    intro X2
    first
    | (have i₁ := eq642502 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq642502
    | (have j0 := eq642502 X2
       grind)
    | exact resolve eq642502 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq642502
  have eq643240 : ∀ X2 : G, (M.op X2 x) = (k X2 x) := by
    intro X2
    first
    | (have j0 := eq642926 X2
       grind)
    | (have r₁ := eq642926 X2
       have r₂ := eq562371
       grind)
    | exact resolve eq642926 eq562371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642926
  have eq647235 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq634645 eq33645
    | exact resolve eq33645 eq634645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33645 eq634645
  have eq647296 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1160 eq647235
    | exact resolve eq647235 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq647235
  have eq647562 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1180 eq647296
    | exact resolve eq647296 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq647296
  have eq647788 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq562571 eq647562
    | exact resolve eq647562 eq562571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562571 eq647562
  have eq647965 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq43109 eq647788
    | exact resolve eq647788 eq43109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43109 eq647788
  have eq648111 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1186 eq647965
    | exact resolve eq647965 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186 eq647965
  have eq648214 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) x) := by
    first
    | exact superpose eq570023 eq648111
    | exact resolve eq648111 eq570023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648111
  have eq655164 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq643240 y
       grind)
    | exact superpose eq643240 eq71
    | exact resolve eq71 eq643240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq655173 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq643240 sF0
       grind)
    | exact superpose eq643240 eq124
    | exact resolve eq124 eq643240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq655245 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq562558 eq655173
    | exact resolve eq655173 eq562558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562558 eq655173
  have eq655279 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq655245
    | exact resolve eq655245 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655245
  have eq679268 : ∀ X0 : G, (M.op (σ x) (M.op y X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2505 X0
       have i₂ := eq134704 (M.op sF4 (M.op X0 sF3)) sF0
       grind)
    | exact superpose eq134704 eq2505
    | exact resolve eq2505 eq134704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505
  have eq679269 : ∀ X0 : G, (M.op (σ x) (M.op y X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op X0 (σ y))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq679268 X0
       have i₂ := eq134704 sF4 (M.op X0 sF3)
       grind)
    | exact superpose eq134704 eq679268
    | exact resolve eq679268 eq134704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134704 eq679268
  have eq679270 : ∀ X0 : G, (M.op (σ x) (M.op y X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq679269 X0
       have i₂ := eq15150 (M.op sF4 x) (M.op X0 sF3) sF0
       grind)
    | (have i₁ := eq679269 X0
       have i₂ := eq15150 (M.op sF4 x) sF0 (M.op X0 sF3)
       grind)
    | exact superpose eq15150 eq679269
    | exact resolve eq679269 eq15150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15150 eq679269
  have eq679271 : ∀ X0 : G, (M.op (σ x) (M.op y X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq648214 eq679270
    | exact resolve eq679270 eq648214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648214 eq679270
  have eq679345 : (M.op (σ x) (M.op y (M.op x (σ x)))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) y))) := by
    first
    | exact superpose eq26246 eq679271
    | exact resolve eq679271 eq26246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26246
  have eq680045 : (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op x (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op y (M.op x (σ x)))) := by
    first
    | exact superpose eq1166 eq679345
    | exact resolve eq679345 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166 eq679345
  have eq680410 : (M.op (σ x) (M.op (M.op x y) (σ x))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq680045
       have i₂ := eq22631 sF2 sF2
       grind)
    | exact superpose eq22631 eq680045
    | exact resolve eq680045 eq22631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22631 eq680045
  have eq680725 : (M.op (σ x) (M.op (M.op x y) (σ x))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op x (σ y))) := by
    first
    | exact superpose eq569405 eq680410
    | exact resolve eq680410 eq569405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680410
  have eq680979 : (M.op (σ x) (M.op y x)) = (M.op (σ x) (M.op (M.op x y) (σ x))) := by
    first
    | exact superpose eq679271 eq680725
    | exact resolve eq680725 eq679271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680725
  have eq681134 : (M.op (σ x) (M.op (M.op x y) x)) = (M.op (σ x) (M.op y x)) := by
    first
    | exact superpose eq570458 eq680979
    | exact resolve eq680979 eq570458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680979
  have eq681232 : (M.op (σ x) (M.op x y)) = (M.op (σ x) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq681134
       have i₂ := eq3093 sF2
       grind)
    | exact superpose eq3093 eq681134
    | exact resolve eq681134 eq3093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093 eq681134
  have eq681288 : (M.op (σ x) (M.op x y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq894 eq681232
    | exact resolve eq681232 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq681232
  have eq682963 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) y))) := by
    first
    | exact superpose eq681288 eq113300
    | exact resolve eq113300 eq681288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113300
  have eq683172 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (σ x) (M.op (σ x) y))) := by
    intro X0
    first
    | exact superpose eq681288 eq11237
    | exact resolve eq11237 eq681288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681288
  have eq683251 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq683172 X0
       have i₂ := eq11237 X0 y sF2
       grind)
    | exact superpose eq11237 eq683172
    | exact resolve eq683172 eq11237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11237 eq683172
  have eq683452 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op y (σ x)))) := by
    first
    | (have i₁ := eq682963
       have i₂ := eq56577 sF2 y sF4
       grind)
    | (have i₁ := eq682963
       have i₂ := eq56577 y sF2 sF4
       grind)
    | exact superpose eq56577 eq682963
    | exact resolve eq682963 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682963
  have eq683684 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op y (σ y))) := by
    first
    | exact superpose eq391881 eq683452
    | exact resolve eq683452 eq391881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391881 eq683452
  have eq683885 : (σ x) = (M.op (σ x) (M.op y y)) := by
    first
    | exact superpose eq679271 eq683684
    | exact resolve eq683684 eq679271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679271 eq683684
  have eq693479 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq683885
       have i₂ := eq119140 sF2 x y
       grind)
    | (have i₁ := eq683885
       have i₂ := eq119140 sF2 y x
       grind)
    | exact superpose eq119140 eq683885
    | exact resolve eq683885 eq119140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119140 eq683885
  have eq698642 : ∀ X1 X2 : G, (σ x) ≠ (M.op (M.op (σ x) (M.op X1 (σ x))) X1) ∨ (M.op X2 (σ x)) = (k X2 (σ x)) := by
    intro X1 X2
    first
    | exact superpose eq693479 eq392
    | exact resolve eq392 eq693479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq693479
  have eq698972 : ∀ X2 : G, (σ x) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X2 (σ x)) = (k X2 (σ x)) := by
    intro X2
    first
    | exact superpose eq215 eq698642
    | (have j0 := eq698642 x X2
       grind)
    | exact resolve eq698642 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq698642
  have eq699404 : ∀ X2 : G, (σ x) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X2 (σ x)) = (k X2 (σ x)) := by
    intro X2
    first
    | exact superpose eq26 eq698972
    | (have j0 := eq698972 X2
       grind)
    | exact resolve eq698972 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698972
  have eq699741 : ∀ X2 : G, (M.op X2 (σ x)) = (k X2 (σ x)) := by
    intro X2
    first
    | (have j0 := eq699404 X2
       grind)
    | (have r₁ := eq699404 X2
       have r₂ := eq570988
       grind)
    | exact resolve eq699404 eq570988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570988 eq699404
  have eq699955 : ∀ X2 : G, (M.op X2 x) = (k X2 (σ x)) := by
    intro X2
    first
    | exact superpose eq570458 eq699741
    | exact resolve eq699741 eq570458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699741
  have eq700366 : ∀ X0 : G, (M.op X0 (M.op (σ y) x)) = (M.op (M.op (M.op (M.op X0 y) (M.op x y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq134701 eq2925
    | exact resolve eq2925 eq134701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925 eq134701
  have eq700367 : ∀ X0 : G, (M.op X0 (M.op (σ y) x)) = (M.op (M.op (M.op (M.op X0 y) (M.op x y)) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq569405 eq700366
    | exact resolve eq700366 eq569405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569405 eq700366
  have eq700368 : ∀ X0 : G, (M.op X0 (M.op (σ y) x)) = (M.op (M.op (M.op (M.op X0 y) (M.op x y)) x) (σ y)) := by
    intro X0
    first
    | exact superpose eq570458 eq700367
    | exact resolve eq700367 eq570458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700367
  have eq700369 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) x)) := by
    intro X0
    first
    | exact superpose eq53 eq700368
    | exact resolve eq700368 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq700368
  have eq700370 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op x (σ y))) := by
    intro X0
    first
    | (have i₁ := eq700369 x
       have i₂ := eq56577 sF3 x x
       grind)
    | (have i₁ := eq700369 x
       have i₂ := eq56577 x sF3 x
       grind)
    | exact superpose eq56577 eq700369
    | exact resolve eq700369 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700369
  have eq716451 : (σ (M.op x y)) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq655279 eq699955
    | exact resolve eq699955 eq655279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655279
  have eq716455 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) x) := by
    intro X0
    first
    | exact superpose eq699955 eq39
    | exact resolve eq39 eq699955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq716535 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq716455 X0
       have i₂ := eq643240 X0
       grind)
    | exact superpose eq643240 eq716455
    | exact resolve eq716455 eq643240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643240 eq716455
  have eq716799 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq716451 eq14711
    | exact resolve eq14711 eq716451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14711
  have eq716867 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq716451 eq716799
    | exact resolve eq716799 eq716451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716451 eq716799
  have eq773358 : (σ (M.op y x)) = (M.op (σ y) x) := by
    first
    | exact superpose eq699955 eq655164
    | exact resolve eq655164 eq699955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655164 eq699955
  have eq944347 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (σ x)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq585411 eq46813
    | exact resolve eq46813 eq585411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46813 eq585411
  have eq944348 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 x) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq570458 eq944347
    | exact resolve eq944347 eq570458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570458 eq944347
  have eq1852214 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq562356 eq103
    | exact resolve eq103 eq562356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1852215 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1852214
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1852214
    | exact resolve eq1852214 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852214
  have eq1852216 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq562371 eq1852215
    | exact resolve eq1852215 eq562371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562371 eq1852215
  have eq1852228 : (τ (σ x)) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1852216 eq108
    | exact resolve eq108 eq1852216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1852216
  have eq1852247 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq28 eq1852228
    | exact resolve eq1852228 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852228
  have eq4866711 : (M.op x y) = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq11239 y
       have i₂ := eq1852247
       grind)
    | exact superpose eq1852247 eq11239
    | exact resolve eq11239 eq1852247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11239 eq1852247
  have eq4867457 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq4866711
       have i₂ := eq640366
       grind)
    | exact superpose eq640366 eq4866711
    | exact resolve eq4866711 eq640366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640366 eq4866711
  have eq4867458 : x = (k y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq4867457
  have eq4868741 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ x) X0) (M.op (M.op X0 X1) (M.op (σ y) X1))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4867458 eq574
    | (have j0 := eq574 y y x x
       grind)
    | exact resolve eq574 eq4867458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq4867458
  have eq4868747 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) X0) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4868741 X0 x
       have i₂ := eq999 (M.op (σ x) X0) (σ y) X0 x
       grind)
    | exact superpose eq999 eq4868741
    | exact resolve eq4868741 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq4868741
  have eq4868769 : (σ (M.op x y)) = (M.op (M.op (σ x) x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4868747 x
       have i₂ := eq944348 (σ x) x (σ y)
       grind)
    | exact superpose eq944348 eq4868747
    | exact resolve eq4868747 eq944348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944348 eq4868747
  have eq4868786 : (σ (M.op x y)) = (M.op (M.op (σ x) x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4868769
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4868769
    | exact resolve eq4868769 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4868769
  have eq4868796 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4868786
       have i₂ := eq716535 x
       grind)
    | exact superpose eq716535 eq4868786
    | exact resolve eq4868786 eq716535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716535 eq4868786
  have eq4868805 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4868796
       have i₂ := eq462173
       grind)
    | exact superpose eq462173 eq4868796
    | exact resolve eq4868796 eq462173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462173 eq4868796
  have eq4868813 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2303 eq4868805
    | exact resolve eq4868805 eq2303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303 eq4868805
  have eq4868821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq570023 eq4868813
    | exact resolve eq4868813 eq570023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570023 eq4868813
  have eq4868829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4868821
    | exact resolve eq4868821 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4868821
  have eq4868837 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4868829
       have r₂ := eq27
       grind)
    | exact resolve eq4868829 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4868829
  have eq4868845 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4868837
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4868837
    | exact resolve eq4868837 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4868837
  have eq4868853 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4868845
    | exact resolve eq4868845 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4868845
  have eq4868860 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq564046 eq4868853
    | exact resolve eq4868853 eq564046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564046 eq4868853
  have eq5008917 : (τ (σ y)) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4868860 eq65760
    | exact resolve eq65760 eq4868860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65760 eq4868860
  have eq5009888 : (τ (σ y)) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5008917
       have i₂ := eq462738
       grind)
    | exact superpose eq462738 eq5008917
    | exact resolve eq5008917 eq462738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462738 eq5008917
  have eq5010213 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5009888
    | exact resolve eq5009888 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5009888
  have eq5017999 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq642661 y
       have i₂ := eq5010213
       grind)
    | exact superpose eq5010213 eq642661
    | exact resolve eq642661 eq5010213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642661 eq5010213
  have eq5018726 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq562356 eq5017999
    | exact resolve eq5017999 eq562356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562356 eq5017999
  have eq5018727 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5018726
  have eq5020015 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5018727 eq28
    | exact resolve eq28 eq5018727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5018727
  have eq5020800 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq5020015
    | exact resolve eq5020015 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5020015
  have eq5020801 : x = (M.op x y) := by grind
  clear eq5020800
  have eq5021555 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq5020801 eq20
    | exact resolve eq20 eq5020801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq5021869 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq5020801 eq683251
    | exact resolve eq683251 eq5020801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683251 eq5020801
  have eq5022446 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5021555
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5021555
    | exact resolve eq5021555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5021555
  have eq5023181 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5022446 eq26
    | exact resolve eq26 eq5022446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5022446
  have eq5045607 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq462795
       have i₂ := eq5021869 y
       grind)
    | exact superpose eq5021869 eq462795
    | exact resolve eq462795 eq5021869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462795 eq5021869
  have eq5046164 : (M.op (σ y) (σ y)) = (M.op (σ y) x) := by
    first
    | (have i₁ := eq5045607
       have i₂ := eq773358
       grind)
    | exact superpose eq773358 eq5045607
    | exact resolve eq5045607 eq773358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773358 eq5045607
  have eq5060061 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) x)) := by
    first
    | exact superpose eq5046164 eq716867
    | exact resolve eq716867 eq5046164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716867 eq5046164
  have eq5060824 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op x (σ y))) := by
    first
    | (have i₁ := eq5060061
       have i₂ := eq56577 sF3 x sF1
       grind)
    | (have i₁ := eq5060061
       have i₂ := eq56577 x sF3 sF1
       grind)
    | exact superpose eq56577 eq5060061
    | exact resolve eq5060061 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56577 eq5060061
  have eq5061278 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq700370 eq5060824
    | exact resolve eq5060824 eq700370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700370 eq5060824
  have eq5061688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5023181 eq5061278
    | exact resolve eq5061278 eq5023181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023181 eq5061278
  have eq5062037 : False := by grind
  exact eq5062037

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_y_pyy_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq31 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq12
    | (have j0 := eq12 X0 (M.op X0 (M.op X0 X1))
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op X0 x))
       have r₂ := eq31 X0 x
       grind)
    | exact resolve eq12 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq97 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (k (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (M.op X0 (M.op X0 x)) X0
       have i₂ := eq31 X0 x
       grind)
    | exact superpose eq31 eq40
    | exact resolve eq40 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq102 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 x
       have i₂ := eq31 X0 x
       grind)
    | exact superpose eq31 eq97
    | exact resolve eq97 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq116 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) (M.op (σ X0) X1)) X0
       have i₂ := eq102 (σ X0) X1
       grind)
    | exact superpose eq102 eq22
    | exact resolve eq22 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq102
  have eq119 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq207 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq78 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq78 X0 X0
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq234 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq235 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq238 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq242 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq238 X0 X1
       have j1 := eq232 X1 X0
       grind)
    | (have r₁ := eq238 X1 X0
       have r₂ := eq232 X0 X1
       grind)
    | (have r₁ := eq238 X1 X1
       have r₂ := eq232 X1 X1
       grind)
    | exact resolve eq238 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq238
  have eq947 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq242
    | exact resolve eq242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq959 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq242 y x
       grind)
    | exact superpose eq242 eq16
    | (have j1 := eq242 y x
       grind)
    | exact resolve eq16 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq990 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq947 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq947
    | (have j0 := eq947 X0 X1
       grind)
    | exact resolve eq947 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq947
  have eq995 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq990 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq990
    | exact resolve eq990 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1135 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq995 (τ X1) X0
       grind)
    | exact superpose eq995 eq18
    | (have j1 := eq995 (τ X1) X0
       grind)
    | exact resolve eq18 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1700 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1135 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1135
    | exact resolve eq1135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1757 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1700 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1700
    | (have j0 := eq1700 X0 X1
       grind)
    | exact resolve eq1700 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq1882 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq959
       have i₂ := eq1757 y x
       grind)
    | exact superpose eq1757 eq959
    | (have j1 := eq1757 (σ y) (σ x)
       grind)
    | (have r₁ := eq959
       have r₂ := eq1757 y x
       grind)
    | exact resolve eq959 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1883 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1882
  have eq1888 : x ≠ x ∨ y = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1883
       grind)
    | exact superpose eq1883 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1883
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1883
       grind)
    | exact resolve eq12 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1890 : y = (M.op (M.op y x) y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq1883
       grind)
    | exact superpose eq1883 eq31
    | exact resolve eq31 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1910 : y = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1888
  have eq1957 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq959
       have i₂ := eq1910
       grind)
    | exact superpose eq1910 eq959
    | exact resolve eq959 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq1910
  have eq1962 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1957
  have eq1963 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1890
       have i₂ := eq1883
       grind)
    | exact superpose eq1883 eq1890
    | exact resolve eq1890 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883 eq1890
  have eq1991 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1963
  have eq2167 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1962
       have i₂ := eq1991
       grind)
    | exact superpose eq1991 eq1962
    | exact resolve eq1962 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962 eq1991
  have eq2168 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq2167
  have eq2169 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq2168
  have eq2230 : y = (k (τ (M.op (σ y) (σ x))) y) := by
    first
    | (have i₁ := eq119 y (σ x)
       have i₂ := eq2169
       grind)
    | exact superpose eq2169 eq119
    | exact resolve eq119 eq2169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq2237 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq31 (σ y) (σ x)
       have i₂ := eq2169
       grind)
    | exact superpose eq2169 eq31
    | exact resolve eq31 eq2169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2269 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2237
       have i₂ := eq2169
       grind)
    | exact superpose eq2169 eq2237
    | exact resolve eq2237 eq2169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237
  have eq2273 : y = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq2169
       grind)
    | exact superpose eq2169 eq2230
    | exact resolve eq2230 eq2169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169 eq2230
  have eq2276 : y = (k x y) := by
    first
    | (have i₁ := eq2273
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2273
    | exact resolve eq2273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq2282 : y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq995 y x
       have i₂ := eq2276
       grind)
    | exact superpose eq2276 eq995
    | (have j0 := eq995 x y
       grind)
    | exact resolve eq995 eq2276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq2276
  have eq2467 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2269
       grind)
    | exact superpose eq2269 eq16
    | exact resolve eq16 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2591 : (σ y) ≠ (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2467
       have i₂ := eq2282
       grind)
    | exact superpose eq2282 eq2467
    | exact resolve eq2467 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq2622 : x = (M.op y x) := by grind
  clear eq2591
  have eq2707 : y = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq2622
       grind)
    | exact superpose eq2622 eq31
    | exact resolve eq31 eq2622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2739 : y = (M.op x y) := by
    first
    | (have i₁ := eq2707
       have i₂ := eq2622
       grind)
    | exact superpose eq2622 eq2707
    | exact resolve eq2707 eq2622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2622 eq2707
  have eq2741 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2467
       have i₂ := eq2739
       grind)
    | exact superpose eq2739 eq2467
    | exact resolve eq2467 eq2739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467 eq2739
  have eq2772 : False := by grind
  exact eq2772

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq85
  have eq239 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq260 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq239 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq266 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq260 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq260 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq260 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq260 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq278 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       have j1 := eq81 X0 (σ X1)
       grind)
    | (have r₁ := eq266 X0 X1
       have r₂ := eq81 X0 (σ X1)
       grind)
    | exact resolve eq266 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq266
  have eq286 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq278
    | (have j0 := eq278 X0 X1
       grind)
    | exact resolve eq278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq287 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq293 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq287 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq287
    | exact resolve eq287 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq287 x y
       grind)
    | exact superpose eq287 eq16
    | exact resolve eq16 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq450 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq293 X0 (τ X1)
       grind)
    | exact superpose eq293 eq17
    | exact resolve eq17 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq293
  have eq466 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq450
    | exact resolve eq450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq474 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq466
    | exact resolve eq466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq489 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq305
       have i₂ := eq474 x y
       grind)
    | exact superpose eq474 eq305
    | exact resolve eq305 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq474
  have eq490 : False := by grind
  exact eq490

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq82
    | exact resolve eq82 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq141 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq166 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq106
    | exact resolve eq106 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq317 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq204 X0
       grind)
    | exact superpose eq204 eq9
    | exact resolve eq9 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq584 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq141
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq141
    | (have j1 := eq55 (σ y) (σ x)
       grind)
    | exact resolve eq141 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq584
  have eq653 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (τ X0) (τ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq317 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq317
    | exact resolve eq317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq670 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq653
    | exact resolve eq653 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq653
  have eq741 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq670 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq670
    | exact resolve eq670 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq670 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq166 X0 (σ X0)
       grind)
    | exact superpose eq166 eq670
    | exact resolve eq670 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq909 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq741 x y
       have i₂ := eq585
       grind)
    | exact superpose eq585 eq741
    | exact resolve eq741 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq3438 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq741 (σ x) (σ y)
       have i₂ := eq909
       grind)
    | exact superpose eq909 eq741
    | exact resolve eq741 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq909
  have eq3443 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3438
       have i₂ := eq94 x
       grind)
    | exact superpose eq94 eq3438
    | exact resolve eq3438 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438
  have eq3576 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq3443
       grind)
    | exact superpose eq3443 eq10
    | exact resolve eq10 eq3443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq3627 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3576
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3576
    | exact resolve eq3576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3576
  have eq3628 : x = (M.op x x) := by grind
  clear eq3627
  have eq3677 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq3628
       grind)
    | exact superpose eq3628 eq12
    | (have j0 := eq12 X0 x
       grind)
    | exact resolve eq12 eq3628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3758 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq3677 X0
       have j1 := eq55 X0 x
       grind)
    | (have r₁ := eq3677 X0
       have r₂ := eq55 X0 x
       grind)
    | exact resolve eq3677 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq3677
  have eq4001 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq141
       have i₂ := eq3758 y
       grind)
    | exact superpose eq3758 eq141
    | exact resolve eq141 eq3758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3758
  have eq4002 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4001
  have eq4012 : (σ y) = (M.op (M.op (σ x) (σ (M.op x x))) (σ y)) := by
    first
    | (have i₁ := eq166 x (σ y)
       have i₂ := eq4002
       grind)
    | exact superpose eq4002 eq166
    | exact resolve eq166 eq4002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq4076 : (σ y) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq4012
       have i₂ := eq742 x
       grind)
    | exact superpose eq742 eq4012
    | exact resolve eq4012 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq4012
  have eq4089 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4076
       have i₂ := eq3628
       grind)
    | exact superpose eq3628 eq4076
    | exact resolve eq4076 eq3628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3628 eq4076
  have eq4093 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4089
       have i₂ := eq4002
       grind)
    | exact superpose eq4002 eq4089
    | exact resolve eq4089 eq4002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4002 eq4089
  have eq4238 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4093
       grind)
    | exact superpose eq4093 eq10
    | exact resolve eq10 eq4093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4093
  have eq4293 : x = y := by
    first
    | (have i₁ := eq4238
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4238
    | exact resolve eq4238 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238
  have eq4455 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4293
       grind)
    | exact superpose eq4293 eq16
    | exact resolve eq16 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293
  have eq4464 : False := by grind
  exact eq4464
