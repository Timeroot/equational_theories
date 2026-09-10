import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation746`: `x = y ◇ (z ◇ ((x ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_pyy_pyy_pxy_pyx_Equation746 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law746 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law746.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op y (M.op X0 (M.op (M.op x y) X0))) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X0 X2) X1)) (M.op X3 (M.op X0 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X0 X2) X1)) X3
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X0 (M.op X3 X1)) X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 (M.op X2 (M.op (M.op X0 (M.op X3 X1)) X2))
       have i₂ := eq14 X0 (M.op X3 X1) X2
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
  have eq67 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq49
    | exact resolve eq49 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq67
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
  clear eq36
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
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
  clear eq98
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq236 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op (M.op x y) X0)) (M.op X1 (M.op x X1))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (M.op X1 (M.op (σ x) X1))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq396 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op x y) X1)) = (M.op (M.op X0 (M.op x X0)) (M.op X2 (M.op y X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op (M.op X1 (M.op X2 X1)) X0) (M.op X4 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 (M.op X1 (M.op X2 X1)) (M.op (M.op X2 X0) X3) X4
       have i₂ := eq52 X2 X3 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op (M.op X1 X0) X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X4 (M.op (M.op X1 X0) X4)) (M.op X1 X2) X3 X2
       have i₂ := eq52 X1 X4 X0 X2
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X1 X2 (M.op X2 (M.op X0 X2))
       have i₂ := eq53 X2 X2 X1 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X1)) X2) = (M.op X0 (M.op X3 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 X1 (M.op (M.op X1 (M.op X0 X1)) X2) X3
       have i₂ := eq53 X1 X1 X2 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X1)) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X0 X1)) X2) X1
       have i₂ := eq53 X1 X1 X2 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X3 X4))) X1)) X2) X0) (M.op X5 (M.op X3 X5))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X3 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X3 X4))) X1)) X2) X4 X5
       have i₂ := eq53 X2 (M.op X3 X4) X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq946 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq498 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq498
    | (have j0 := eq498 x y X0
       grind)
    | exact resolve eq498 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq498
    | (have j0 := eq498 (σ x) X0 (σ y)
       grind)
    | exact resolve eq498 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X1 X0) X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq498 (M.op (M.op X1 X0) X1) (M.op X1 (M.op (M.op X1 X0) X1)) X2
       have i₂ := eq52 X1 X1 X0 (M.op (M.op X1 X0) X1)
       grind)
    | exact superpose eq52 eq498
    | exact resolve eq498 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) X0) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq501 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq501
    | (have j0 := eq501 x y X0
       grind)
    | exact resolve eq501 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq501
    | (have j0 := eq501 (σ x) (σ y) X0
       grind)
    | exact resolve eq501 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X1 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq501 (M.op (M.op X1 X0) X1) (M.op X1 (M.op (M.op X1 X0) X1)) X2
       have i₂ := eq52 X1 X1 X0 (M.op (M.op X1 X0) X1)
       grind)
    | exact superpose eq52 eq501
    | exact resolve eq501 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X1))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq501 X0 (M.op X1 (M.op X2 X1)) X2
       have i₂ := eq501 X2 X1 (M.op X0 (M.op X1 (M.op X2 X1)))
       grind)
    | exact superpose eq501 eq501
    | exact resolve eq501 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq1072 eq501
    | exact resolve eq501 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1169 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1074 eq501
    | exact resolve eq501 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1179 : ∀ X0 : G, y = (M.op (M.op X0 (M.op (M.op x y) X0)) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq236 X0 x
       have i₂ := eq946 x
       grind)
    | (have i₁ := eq236 X0 y
       have i₂ := eq946 X0
       grind)
    | exact superpose eq946 eq236
    | (have j0 := eq236 X0 y
       grind)
    | exact resolve eq236 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq1180 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1148 sF0
       have i₂ := eq498 y sF0 x
       grind)
    | (have i₁ := eq1148 sF0
       have i₂ := eq498 y x sF0
       grind)
    | exact superpose eq498 eq1148
    | exact resolve eq1148 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1169 sF4
       have i₂ := eq498 sF3 sF4 x
       grind)
    | (have i₁ := eq1169 sF4
       have i₂ := eq498 sF3 x sF4
       grind)
    | exact superpose eq498 eq1169
    | exact resolve eq1169 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq1169
  have eq1260 : ∀ X0 : G, (M.op (M.op y X0) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq1180 eq14
    | exact resolve eq14 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1372 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq1224 eq14
    | exact resolve eq14 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1373 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1224 eq53
    | exact resolve eq53 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1224
  have eq1388 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq948 eq239
    | (have j0 := eq239 X0 (σ y)
       grind)
    | exact resolve eq239 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq948
  have eq1469 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq1260 eq501
    | exact resolve eq501 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1541 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq1372 eq501
    | exact resolve eq501 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq1372
  have eq2148 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1373 (M.op (M.op x sF4) x)
       have i₂ := eq1081 sF4 x sF2
       grind)
    | exact superpose eq1081 eq1373
    | exact resolve eq1373 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq1373
  have eq2266 : (σ y) = (M.op (M.op x (M.op (M.op (σ x) (σ y)) (M.op y (M.op x y)))) (σ x)) := by
    first
    | exact superpose eq1148 eq2148
    | exact resolve eq2148 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq2148
  have eq5901 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X0) X1) (M.op X3 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq500 (M.op (M.op X1 X0) X1) (M.op X1 (M.op (M.op X1 X0) X1)) X2 X3
       have i₂ := eq52 X1 X1 X0 (M.op (M.op X1 X0) X1)
       grind)
    | exact superpose eq52 eq500
    | exact resolve eq500 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq500
  have eq6387 : ∀ X1 X2 : G, (M.op X1 (M.op (M.op x y) X1)) = (M.op (M.op y (M.op x y)) (M.op X2 (M.op y X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq396 x X1 X2
       have i₂ := eq946 x
       grind)
    | (have i₁ := eq396 y X1 X2
       have i₂ := eq946 x
       grind)
    | exact superpose eq946 eq396
    | (have j0 := eq396 y X1 X2
       grind)
    | exact resolve eq396 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq946
  have eq12057 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op (M.op (M.op X3 (M.op y X3)) (M.op X0 (M.op (M.op x y) X0))) (M.op X4 (M.op (M.op X1 (M.op y (M.op x y))) X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq6387 eq492
    | exact resolve eq492 eq6387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq6387
  have eq12657 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op y (M.op X0 (M.op (M.op x y) X0))) (M.op X1 (M.op y (M.op x y))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12057 X0 X1 X2 X1 x
       have i₂ := eq399 (M.op X0 (M.op sF0 X0)) X1 y (M.op X1 (M.op y sF0)) x
       grind)
    | exact superpose eq399 eq12057
    | exact resolve eq12057 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12057
  have eq12708 : ∀ X1 X2 : G, (M.op (M.op X1 X2) (M.op x (M.op X1 (M.op y (M.op x y))))) = X2 := by
    intro X1 X2
    first
    | exact superpose eq50 eq12657
    | exact resolve eq12657 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq12657
  have eq21804 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 y) X0)) X1) (M.op X2 (M.op (M.op x y) X2))) (M.op X3 (M.op y X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1179 eq507
    | exact resolve eq507 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq21806 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (σ y)) X0)) X1) (M.op X2 (M.op (M.op (σ x) (σ y)) X2))) (M.op X3 (M.op (σ y) X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1388 eq507
    | exact resolve eq507 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq1388
  have eq22485 : ∀ X1 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op X1 (σ y)) X1) (M.op (σ x) (σ y))) (M.op X3 (M.op (σ y) X3))) := by
    intro X1 X3
    first
    | (have i₁ := eq21806 X1 x x X3
       have i₂ := eq399 x X1 (M.op x sF3) sF4 x
       grind)
    | exact superpose eq399 eq21806
    | exact resolve eq21806 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21806
  have eq22487 : ∀ X1 X3 : G, (M.op x y) = (M.op (M.op (M.op (M.op X1 y) X1) (M.op x y)) (M.op X3 (M.op y X3))) := by
    intro X1 X3
    first
    | (have i₁ := eq21804 X1 x x X3
       have i₂ := eq399 x X1 (M.op x y) sF0 x
       grind)
    | exact superpose eq399 eq21804
    | exact resolve eq21804 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq21804
  have eq22571 : ∀ X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (M.op X3 (M.op (σ y) X3))) := by
    intro X3
    first
    | exact superpose eq1541 eq22485
    | (have j0 := eq22485 (σ x) X3
       grind)
    | exact resolve eq22485 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541 eq22485
  have eq22572 : ∀ X3 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op X3 (M.op y X3))) := by
    intro X3
    first
    | (have i₁ := eq22487 x X3
       have i₂ := eq1469 x
       grind)
    | (have i₁ := eq22487 x X3
       have i₂ := eq1469 x
       grind)
    | exact superpose eq1469 eq22487
    | (have j0 := eq22487 x X3
       grind)
    | exact resolve eq22487 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469 eq22487
  have eq64926 : ∀ X0 X1 : G, (M.op (M.op x (M.op (M.op X0 X1) (M.op y (M.op x y)))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq12708 eq953
    | exact resolve eq953 eq12708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq12708
  have eq295388 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op x (M.op x x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq22572 x
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq22572
    | exact resolve eq22572 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq22572
  have eq295722 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq295388
       have i₂ := eq5901 x sF0 x x
       grind)
    | exact superpose eq5901 eq295388
    | exact resolve eq295388 eq5901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295388
  have eq295723 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq295722
  have eq295765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq295723 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq295723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295723
  have eq295772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq295765
    | exact resolve eq295765 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295765
  have eq295783 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq295772
       have r₂ := eq27
       grind)
    | exact resolve eq295772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295772
  have eq295787 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq295783
    | exact resolve eq295783 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295783
  have eq295797 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ x)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq295787 eq22571
    | exact resolve eq22571 eq295787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22571 eq295787
  have eq296131 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq295797
       have i₂ := eq5901 sF2 sF4 sF2 sF2
       grind)
    | exact superpose eq5901 eq295797
    | exact resolve eq295797 eq5901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5901 eq295797
  have eq296132 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq296131
  have eq296389 : (σ x) = (M.op (M.op x (M.op (M.op (σ x) (σ y)) (M.op y (M.op x y)))) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq296132 eq64926
    | exact resolve eq64926 eq296132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296132
  have eq296392 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2266 eq296389
    | exact resolve eq296389 eq2266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266 eq296389
  have eq296733 : x = (M.op (M.op x (M.op (M.op x y) (M.op y (M.op x y)))) x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64926 x x
       have i₂ := eq296392
       grind)
    | exact superpose eq296392 eq64926
    | exact resolve eq64926 eq296392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64926 eq296392
  have eq296736 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq296733
       have i₂ := eq1083 x sF0 y
       grind)
    | exact superpose eq1083 eq296733
    | exact resolve eq296733 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq296733
  have eq296871 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq296736 eq29
    | exact resolve eq29 eq296736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq296736
  have eq297178 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq296871
    | exact resolve eq296871 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq296871
  have eq297179 : x = y := by grind
  clear eq297178
  have eq297202 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq297179
       grind)
    | exact superpose eq297179 eq18
    | exact resolve eq18 eq297179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq297203 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq297179
       grind)
    | exact superpose eq297179 eq24
    | exact resolve eq24 eq297179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq297179
  have eq297518 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq297203
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq297203
    | exact resolve eq297203 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq297203
  have eq297567 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq297518 eq26
    | exact resolve eq26 eq297518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq297518
  have eq298459 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq297567 eq68
    | exact resolve eq68 eq297567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq297567
  have eq298837 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq298459
       have i₂ := eq297202
       grind)
    | exact superpose eq297202 eq298459
    | exact resolve eq298459 eq297202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297202 eq298459
  have eq298925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq298837 eq15
    | exact resolve eq15 eq298837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298837
  have eq299009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq298925
    | exact resolve eq298925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq298925
  have eq299030 : False := by grind
  exact eq299030

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_y_pxy_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op y (M.op (M.op x y) (M.op X0 y))) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq132 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq215 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ x)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq7458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq7459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq7458
    | exact resolve eq7458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7458
  have eq7470 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq7459
       have r₂ := eq27
       grind)
    | exact resolve eq7459 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7459
  have eq7472 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq7470
    | exact resolve eq7470 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7470
  have eq8049 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq7472 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq7472
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7472
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq7472
       grind)
    | exact resolve eq13 eq7472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7472
  have eq8062 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq8049
  have eq8071 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq8062 eq99
    | exact resolve eq99 eq8062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq8062
  have eq8094 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq8071
    | exact resolve eq8071 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8071
  have eq8097 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq8094
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq8094
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq8094
       have r₂ := eq13 y x
       grind)
    | exact resolve eq8094 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8094
  have eq8116 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq692 x y
       have i₂ := eq8097
       grind)
    | exact superpose eq8097 eq692
    | (have j0 := eq692 x y
       grind)
    | exact resolve eq692 eq8097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8118 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq8097
       grind)
    | exact superpose eq8097 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq8097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8097
  have eq8119 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8118
  have eq8121 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8116
  have eq8123 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8119
    | exact resolve eq8119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8119
  have eq8124 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8123
  have eq8126 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8121
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8121
    | exact resolve eq8121 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8121
  have eq8137 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8126
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8126
    | exact resolve eq8126 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8126
  have eq8139 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8137
    | exact resolve eq8137 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8137
  have eq8140 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8139
  have eq8142 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8140
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8140
    | exact resolve eq8140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8140
  have eq8144 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8142
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8142
    | exact resolve eq8142 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8142
  have eq8145 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8124
       grind)
    | exact superpose eq8124 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8124
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8124
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8124
       grind)
    | exact resolve eq12 eq8124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8124
  have eq8160 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8145
  have eq8161 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8160
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8160
    | exact resolve eq8160 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8160
  have eq8162 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8161
  have eq8163 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8162
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8162
    | exact resolve eq8162 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8162
  have eq8208 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8144 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8144
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8144
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8144
       grind)
    | exact resolve eq12 eq8144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8144
  have eq8223 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8208
  have eq8224 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8223
    | exact resolve eq8223 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8223
  have eq8225 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8224
  have eq8226 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8225
    | exact resolve eq8225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8225
  have eq8228 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq8163
       grind)
    | exact superpose eq8163 eq44
    | exact resolve eq44 eq8163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8163
  have eq8246 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8228
    | exact resolve eq8228 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8228
  have eq8299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8246 eq8226
    | exact resolve eq8226 eq8246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8226 eq8246
  have eq8303 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8299
  have eq8305 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8303
       have r₂ := eq27
       grind)
    | exact resolve eq8303 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8303
  have eq8317 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8305 eq51
    | (have r₁ := eq51
       have r₂ := eq8305
       grind)
    | exact resolve eq51 eq8305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq8305
  have eq8332 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8317
  have eq8348 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8332 eq55
    | exact resolve eq55 eq8332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq8332
  have eq8375 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8348
    | exact resolve eq8348 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8348
  have eq8379 : y = (k x y) := by
    first
    | (have r₁ := eq8375
       have r₂ := eq50
       grind)
    | exact resolve eq8375 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq8375
  have eq8382 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq8379
       grind)
    | exact superpose eq8379 eq44
    | exact resolve eq44 eq8379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8390 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq692 y x
       have i₂ := eq8379
       grind)
    | exact superpose eq8379 eq692
    | (have j0 := eq692 y x
       grind)
    | exact resolve eq692 eq8379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq8392 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq8379
       grind)
    | exact superpose eq8379 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq8379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8393 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq8392
  have eq8395 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8390
  have eq8397 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8393
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8393
    | exact resolve eq8393 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8393
  have eq8399 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8395
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8395
    | exact resolve eq8395 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8395
  have eq8406 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq8382
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8382
    | exact resolve eq8382 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8382
  have eq8409 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8399
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8399
    | exact resolve eq8399 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8399
  have eq8411 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8409
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8409
    | exact resolve eq8409 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8409
  have eq8413 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8411
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8411
    | exact resolve eq8411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8411
  have eq8415 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8413
    | exact resolve eq8413 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8413
  have eq8459 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq8397
       grind)
    | exact superpose eq8397 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8397
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8397
       grind)
    | exact resolve eq12 eq8397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8461 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq8397
       grind)
    | exact superpose eq8397 eq14
    | exact resolve eq14 eq8397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8474 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq8459
  have eq8475 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8474
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8474
    | exact resolve eq8474 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8474
  have eq8476 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq8475
  have eq8477 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8476
       have i₂ := eq8379
       grind)
    | exact superpose eq8379 eq8476
    | exact resolve eq8476 eq8379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8379 eq8476
  have eq8478 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8477
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8477
    | exact resolve eq8477 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8477
  have eq8482 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8478 eq56
    | exact resolve eq56 eq8478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq8528 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8478 eq215
    | exact resolve eq215 eq8478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq8478
  have eq8817 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8415 eq14
    | exact resolve eq14 eq8415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16912 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8461 y
       have i₂ := eq8397
       grind)
    | exact superpose eq8397 eq8461
    | exact resolve eq8461 eq8397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8397 eq8461
  have eq16935 : x = (M.op x (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq16912
  have eq17604 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8415 eq8817
    | exact resolve eq8817 eq8415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8817
  have eq17636 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17604
  have eq17874 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8482 y
       have i₂ := eq8528
       grind)
    | exact superpose eq8528 eq8482
    | exact resolve eq8482 eq8528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8482 eq8528
  have eq17901 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq17874
  have eq17902 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16935
       have i₂ := eq17901
       grind)
    | exact superpose eq17901 eq16935
    | exact resolve eq16935 eq17901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16935 eq17901
  have eq17954 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17902
  have eq17955 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17954
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17954
    | exact resolve eq17954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17954
  have eq17956 : x = (M.op x y) := by grind
  clear eq17955
  have eq17958 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17956 eq20
    | exact resolve eq20 eq17956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq17977 : (σ (k x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17956 eq132
    | exact resolve eq132 eq17956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq17956
  have eq18074 : (k (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq17977
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq17977
    | exact resolve eq17977 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq17977
  have eq18089 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17958
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17958
    | exact resolve eq17958 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17958
  have eq18097 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq8406 eq18074
    | exact resolve eq18074 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8406 eq18074
  have eq18104 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18089 eq26
    | exact resolve eq26 eq18089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq18178 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18089 eq8415
    | exact resolve eq8415 eq18089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8415
  have eq18200 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18089 eq17636
    | exact resolve eq17636 eq18089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17636 eq18089
  have eq18202 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have r₁ := eq18200
       have r₂ := eq27
       grind)
    | exact resolve eq18200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18200
  have eq18206 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq18178
       have r₂ := eq27
       grind)
    | exact resolve eq18178 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18178
  have eq18608 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18206 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq18206
       grind)
    | exact resolve eq12 eq18206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18206
  have eq18635 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq18608
  have eq18636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18104 eq18635
    | exact resolve eq18635 eq18104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18635
  have eq18637 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq18636
       have r₂ := eq27
       grind)
    | exact resolve eq18636 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18636
  have eq18638 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18104 eq18637
    | exact resolve eq18637 eq18104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18637
  have eq18639 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18097 eq18638
    | exact resolve eq18638 eq18097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18097 eq18638
  have eq18643 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq18639 eq57
    | exact resolve eq57 eq18639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq18646 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq18639 eq228
    | exact resolve eq228 eq18639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq18639
  have eq27358 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq18646 eq18643
    | exact resolve eq18643 eq18646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18643 eq18646
  have eq27406 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27358 eq18202
    | exact resolve eq18202 eq27358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18202 eq27358
  have eq27493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18104 eq27406
    | exact resolve eq27406 eq18104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18104 eq27406
  have eq27515 : False := by grind
  exact eq27515

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_x_pxx_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  clear eq24 eq35
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
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
  have eq66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq43
    | exact resolve eq43 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq49
    | exact resolve eq49 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq72
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq72
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq132
       have i₂ := eq68 sF1
       grind)
    | exact superpose eq68 eq132
    | exact resolve eq132 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq137 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq135
       have i₂ := eq68 sF0
       grind)
    | exact superpose eq68 eq135
    | exact resolve eq135 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq269 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq34
    | exact resolve eq34 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq280 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq269 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq269
    | exact resolve eq269 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq282 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq280
    | exact resolve eq280 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq301 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq412 : (k x (k x x)) = (τ (k (σ x) (k (σ x) (σ x)))) := by
    first
    | exact superpose eq49 eq301
    | exact resolve eq301 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq427 : (k x (k x x)) = (τ (k (σ x) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq412
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq412
    | exact resolve eq412 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq429 : (k x (M.op x x)) = (τ (k (σ x) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq427
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq427
    | exact resolve eq427 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq577 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq577 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq577
    | exact resolve eq577 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq14
    | exact resolve eq14 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq14
    | exact resolve eq14 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X3 (M.op X0 (M.op (M.op X4 X5) (M.op X3 X5))))))) X1)) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X1 X2 X0 (M.op X3 (M.op X0 (M.op (M.op X4 X5) (M.op X3 X5))))
       have i₂ := eq52 X3 X0 X4 X5
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq639 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X0 X0)))) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X2 X0 (M.op X0 X0)
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq55
    | exact resolve eq55 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (M.op X0 X1) X0 X1
       have i₂ := eq577 (M.op X0 X1)
       grind)
    | exact superpose eq577 eq55
    | exact resolve eq55 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq700 : x = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq662 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq662
    | (have j0 := eq662 x y
       grind)
    | exact resolve eq662 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq749 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq282 X0
       grind)
    | exact superpose eq282 eq16
    | exact resolve eq16 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq817 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq818 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq817 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq817
    | (have j0 := eq817 X0 X1
       grind)
    | exact resolve eq817 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq817
  have eq918 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq818 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq994 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op X1 (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq582 X0
       grind)
    | exact superpose eq582 eq14
    | exact resolve eq14 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op X1 (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq588 (τ X0) X1
       have i₂ := eq749 X0
       grind)
    | exact superpose eq749 eq588
    | exact resolve eq588 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq1219 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq588 X0 (M.op X1 X0)
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq588
    | exact resolve eq588 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7769 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X0 X3)))) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X0 X3)))) (M.op (M.op X4 X0) (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X0 X3)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq635 X0 (M.op X1 (M.op X0 (M.op (M.op X2 X3) (M.op X0 X3)))) X4 X0 X2 X3
       have i₂ := eq14 X0 X1 (M.op X0 (M.op (M.op X2 X3) (M.op X0 X3)))
       grind)
    | exact superpose eq14 eq635
    | exact resolve eq635 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq7793 : ∀ X0 X1 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X4 X0) (M.op X1 X0))) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq7769 X0 X1 X1 x X4
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq7769
    | exact resolve eq7769 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7769
  have eq27783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq27783
    | exact resolve eq27783 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27783
  have eq27802 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq27791
       have r₂ := eq27
       grind)
    | exact resolve eq27791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27791
  have eq27806 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq27802
    | exact resolve eq27802 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27802
  have eq27808 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27806 eq66
    | (have r₁ := eq66
       have r₂ := eq27806
       grind)
    | exact resolve eq66 eq27806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq27806
  have eq27884 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq27808
  have eq28472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27884 eq96
    | exact resolve eq96 eq27884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq27884
  have eq28488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq28472
  have eq28491 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq28488
       have r₂ := eq27
       grind)
    | exact resolve eq28488 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28488
  have eq28495 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28491 eq73
    | exact resolve eq73 eq28491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28498 : (τ (k (σ x) (σ x))) = (k x (M.op x x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28491 eq429
    | exact resolve eq429 eq28491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq28491
  have eq28613 : (k x x) = (k x (M.op x x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq49 eq28498
    | exact resolve eq28498 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq28498
  have eq28614 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq28495
    | exact resolve eq28495 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28495
  have eq28615 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq28614
  have eq28621 : (M.op x x) = (k x (M.op x x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq28613
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq28613
    | exact resolve eq28613 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq28613
  have eq28627 : (M.op x x) = (k x (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq586 x
       grind)
    | (have r₁ := eq28621
       have r₂ := eq586 x
       grind)
    | exact resolve eq28621 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq28621
  have eq28629 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65
       have i₂ := eq28615
       grind)
    | exact superpose eq28615 eq65
    | (have r₁ := eq65
       have r₂ := eq28615
       grind)
    | exact resolve eq65 eq28615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq28630 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq28615
       grind)
    | exact superpose eq28615 eq74
    | exact resolve eq74 eq28615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28615
  have eq28705 : (M.op x y) = (k x y) ∨ x = (M.op x x) := by grind
  clear eq28629
  have eq28722 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq28630
    | exact resolve eq28630 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28630
  have eq29132 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq28705
       grind)
    | exact superpose eq28705 eq44
    | exact resolve eq44 eq28705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq28705
  have eq29166 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq29132
    | exact resolve eq29132 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29132
  have eq29464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29166 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq29166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29166
  have eq29474 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq29464
    | exact resolve eq29464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29464
  have eq29485 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29474
       have r₂ := eq27
       grind)
    | exact resolve eq29474 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29474
  have eq29489 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq29485
    | exact resolve eq29485 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29485
  have eq30334 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq918 x (M.op x x)
       have i₂ := eq28627
       grind)
    | exact superpose eq28627 eq918
    | (have j0 := eq918 x (M.op x x)
       grind)
    | exact resolve eq918 eq28627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq28627
  have eq30335 : (σ x) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq30334
  have eq30342 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq30335
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq30335
    | exact resolve eq30335 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30335
  have eq30350 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq30342
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30342
    | exact resolve eq30342 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30342
  have eq30357 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq30350
       have i₂ := eq582 x
       grind)
    | exact superpose eq582 eq30350
    | exact resolve eq30350 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq30350
  have eq30364 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq30357
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq30357
    | exact resolve eq30357 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30357
  have eq30371 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq30364
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30364
    | exact resolve eq30364 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30364
  have eq30372 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq30371
  have eq30427 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = X0 ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30372 eq588
    | exact resolve eq588 eq30372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq30435 : ∀ X0 : G, (M.op X0 (M.op (τ (σ x)) (M.op X0 (τ (σ x))))) = X0 ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30372 eq1211
    | exact resolve eq1211 eq30372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq30440 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30372 eq14
    | exact resolve eq14 eq30372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30372
  have eq30499 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq30440 x
       have i₂ := eq1219 sF2 x
       grind)
    | exact superpose eq1219 eq30440
    | exact resolve eq30440 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30440
  have eq30503 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq30435
    | exact resolve eq30435 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30435
  have eq32842 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30499 eq30427
    | exact resolve eq30427 eq30499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30427 eq30499
  have eq32917 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq32842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32842
  have eq32974 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq74
       have i₂ := eq32917 X0
       grind)
    | (have i₁ := eq74
       have i₂ := eq32917 (M.op x x)
       grind)
    | exact superpose eq32917 eq74
    | (have j1 := eq32917 X0
       grind)
    | exact resolve eq74 eq32917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32917
  have eq33074 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq32974
    | (have j0 := eq32974 X0
       grind)
    | exact resolve eq32974 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32974
  have eq33386 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq33074 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33074
  have eq35608 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq700 eq30503
    | exact resolve eq30503 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35640 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq639 x x X0
       have i₂ := eq30503 x
       grind)
    | exact superpose eq30503 eq639
    | exact resolve eq639 eq30503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq35690 : ∀ X0 : G, x = (M.op x (M.op X0 x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq35640 X0
       have i₂ := eq1219 x X0
       grind)
    | exact superpose eq1219 eq35640
    | exact resolve eq35640 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35640
  have eq35697 : (M.op x y) = (M.op x x) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq35608 eq700
    | exact resolve eq700 eq35608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq35608
  have eq35767 : x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq577 x
       have i₂ := eq35697
       grind)
    | exact superpose eq35697 eq577
    | exact resolve eq577 eq35697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq35697
  have eq35828 : x = (M.op x (M.op x y)) := by grind
  clear eq35767
  have eq35862 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq35828 eq14
    | exact resolve eq14 eq35828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35828
  have eq36414 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq30503 X0
       have i₂ := eq35690 X0
       grind)
    | exact superpose eq35690 eq30503
    | exact resolve eq30503 eq35690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30503 eq35690
  have eq36486 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq36414 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36414
  have eq36490 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq74
       have i₂ := eq36486 X0
       grind)
    | (have i₁ := eq74
       have i₂ := eq36486 x
       grind)
    | exact superpose eq36486 eq74
    | (have j1 := eq36486 X0
       grind)
    | exact resolve eq74 eq36486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36486
  have eq36597 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq36490
    | (have j0 := eq36490 X0
       grind)
    | exact resolve eq36490 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36490
  have eq140800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28722 eq29489
    | exact resolve eq29489 eq28722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28722 eq29489
  have eq141021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by grind
  clear eq140800
  have eq141048 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq141021
       have r₂ := eq27
       grind)
    | exact resolve eq141021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141021
  have eq141060 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq141048
       grind)
    | exact superpose eq141048 eq74
    | exact resolve eq74 eq141048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141048
  have eq141329 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq141060
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq141060
    | exact resolve eq141060 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141060
  have eq141345 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq141329
       have r₂ := eq33386
       grind)
    | exact resolve eq141329 eq33386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33386 eq141329
  have eq141358 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq141345
       have i₂ := eq36597 (M.op sF2 sF2)
       grind)
    | exact superpose eq36597 eq141345
    | (have j1 := eq36597 X0
       grind)
    | exact resolve eq141345 eq36597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36597
  have eq141364 : (τ (σ x)) = (M.op x x) := by
    first
    | exact superpose eq141345 eq73
    | exact resolve eq73 eq141345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq141536 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) := by
    intro X0
    first
    | exact superpose eq141345 eq7793
    | exact resolve eq7793 eq141345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141560 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq141536 x
       have i₂ := eq1219 sF2 x
       grind)
    | exact superpose eq1219 eq141536
    | exact resolve eq141536 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141536
  have eq141638 : x = (M.op x x) := by
    first
    | exact superpose eq28 eq141364
    | exact resolve eq141364 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141364
  have eq141835 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq7793 x x x
       have i₂ := eq141638
       grind)
    | exact superpose eq141638 eq7793
    | exact resolve eq7793 eq141638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7793 eq141638
  have eq141859 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq141835 X0
       have i₂ := eq1219 x X0
       grind)
    | exact superpose eq1219 eq141835
    | exact resolve eq141835 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq141835
  have eq146718 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq141859 X0
       have i₂ := eq141358 X0
       grind)
    | exact superpose eq141358 eq141859
    | exact resolve eq141859 eq141358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141358
  have eq151807 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq146718 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq146718
    | (have j0 := eq146718 y
       grind)
    | exact resolve eq146718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq146718
  have eq152637 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq151807 eq28
    | exact resolve eq28 eq151807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq151807
  have eq153288 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq152637
    | exact resolve eq152637 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq152637
  have eq153289 : x = (M.op x y) := by grind
  clear eq153288
  have eq153372 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq153289 eq20
    | exact resolve eq20 eq153289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq153389 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq153289 eq137
    | exact resolve eq137 eq153289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq153604 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
    intro X0
    first
    | exact superpose eq153289 eq35862
    | exact resolve eq35862 eq153289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35862 eq153289
  have eq153737 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq153604 X0
       have i₂ := eq141859 X0
       grind)
    | exact superpose eq141859 eq153604
    | exact resolve eq153604 eq141859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141859 eq153604
  have eq153891 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq153389
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq153389
    | exact resolve eq153389 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq153389
  have eq153906 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq153372
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq153372
    | exact resolve eq153372 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153372
  have eq153969 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq141345 eq153891
    | exact resolve eq153891 eq141345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141345 eq153891
  have eq154037 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq153906 eq26
    | exact resolve eq26 eq153906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq154859 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq994 x X0
       have i₂ := eq153737 x
       grind)
    | exact superpose eq153737 eq994
    | exact resolve eq994 eq153737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994 eq153737
  have eq155289 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq154859 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq154859
    | (have j0 := eq154859 X0
       grind)
    | exact resolve eq154859 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq154859
  have eq155386 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq141560 eq155289
    | exact resolve eq155289 eq141560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141560 eq155289
  have eq155439 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq153906 eq155386
    | exact resolve eq155386 eq153906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155386
  have eq155477 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq153906 eq153969
    | exact resolve eq153969 eq153906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153906 eq153969
  have eq159672 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq155439 eq587
    | exact resolve eq587 eq155439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq159856 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq155477 eq159672
    | exact resolve eq159672 eq155477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155477 eq159672
  have eq160009 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq155439 eq159856
    | exact resolve eq159856 eq155439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155439 eq159856
  have eq161052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq160009 eq154037
    | exact resolve eq154037 eq160009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154037 eq160009
  have eq162060 : False := by grind
  exact eq162060

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_x_pxx_pyy_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  clear eq17
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq66 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X4) (M.op X0 X4))) X0)))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X0 X1 X2 (M.op (M.op X3 X4) (M.op X0 X4))
       have i₂ := eq9 X0 X3 X4
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq95 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X0 X0)))) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq24
    | exact resolve eq24 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq95
    | exact resolve eq95 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73 x y
       grind)
    | exact superpose eq73 eq16
    | (have j1 := eq73 x y
       grind)
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq68
    | (have j1 := eq73 X0 X0
       grind)
    | exact resolve eq68 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq73
  have eq152 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq563 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X3 (M.op X0 (M.op X2 (M.op (M.op X4 (M.op (M.op X5 X6) (M.op X0 X6))) X0)))) X2)))) = X1 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq66 X2 X1 X3 X0 (M.op (M.op X4 (M.op (M.op X5 X6) (M.op X0 X6))) X0)
       have i₂ := eq24 X0 X4 X5 X6
       grind)
    | exact superpose eq24 eq66
    | exact resolve eq66 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq66
  have eq685 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq100
    | exact resolve eq100 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1390 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq152 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq152
    | (have j0 := eq152 (τ X0)
       grind)
    | exact resolve eq152 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1425 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1390 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1390
    | (have j0 := eq1390 X0
       grind)
    | exact resolve eq1390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1429 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1425 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1425
    | (have j0 := eq1425 X0
       grind)
    | exact resolve eq1425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1436 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1429 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq1429
    | (have j0 := eq1429 (τ X0)
       grind)
    | exact resolve eq1429 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1429
  have eq5592 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq135
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq135
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq135 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq5595 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq5592
  have eq44361 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq118 (σ x) (σ y)
       have i₂ := eq5595
       grind)
    | exact superpose eq5595 eq118
    | exact resolve eq118 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595
  have eq44418 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq44361
  have eq44493 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) X0) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) x
       have i₂ := eq44418
       grind)
    | exact superpose eq44418 eq12
    | (have r₁ := eq12 (σ x) x
       have r₂ := eq44418
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq44418
       grind)
    | exact resolve eq12 eq44418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44418
  have eq44629 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq44493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44493
  have eq44743 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1436 (σ x)
       have i₂ := eq44629 (σ x)
       grind)
    | exact superpose eq44629 eq1436
    | (have j0 := eq1436 (σ x)
       grind)
    | exact resolve eq1436 eq44629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436 eq44629
  have eq44861 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq44743
  have eq44896 : x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44861
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq44861
    | exact resolve eq44861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44861
  have eq44897 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq44896
  have eq45502 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq118 x y
       have i₂ := eq44897
       grind)
    | exact superpose eq44897 eq118
    | exact resolve eq118 eq44897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44897
  have eq45561 : x = (M.op x x) := by grind
  clear eq45502
  have eq45617 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq45561
       grind)
    | exact superpose eq45561 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq45561
       grind)
    | exact resolve eq12 eq45561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45619 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq95 x X0
       have i₂ := eq45561
       grind)
    | exact superpose eq45561 eq95
    | exact resolve eq95 eq45561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq45726 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq685 x x x
       have i₂ := eq45561
       grind)
    | exact superpose eq45561 eq685
    | exact resolve eq685 eq45561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45755 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq45617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45617
  have eq45763 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq45726 X0
       have i₂ := eq118 x X0
       grind)
    | exact superpose eq118 eq45726
    | exact resolve eq45726 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq45726
  have eq46787 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq152 x
       have i₂ := eq45755 x
       grind)
    | exact superpose eq45755 eq152
    | (have j0 := eq152 x
       grind)
    | exact resolve eq152 eq45755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq45755
  have eq46919 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq46787
  have eq49681 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq45619 X0
       have i₂ := eq45763 X0
       grind)
    | exact superpose eq45763 eq45619
    | exact resolve eq45619 eq45763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45619
  have eq49683 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq45763 X0
       have i₂ := eq49681 X0
       grind)
    | exact superpose eq49681 eq45763
    | exact resolve eq45763 eq49681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45763
  have eq49805 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X1 x) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq685 x X1 X0
       have i₂ := eq49681 X0
       grind)
    | exact superpose eq49681 eq685
    | exact resolve eq685 eq49681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq50030 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49805 X0 X0
       have i₂ := eq49681 X0
       grind)
    | exact superpose eq49681 eq49805
    | exact resolve eq49805 eq49681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49805
  have eq52232 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 (M.op (M.op X2 (M.op x (M.op X1 (M.op (M.op X3 (M.op (M.op X4 x) x)) x)))) X1)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq563 x X0 X1 X2 X3 X4 x
       have i₂ := eq45561
       grind)
    | exact superpose eq45561 eq563
    | exact resolve eq563 eq45561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq45561
  have eq52456 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op (M.op X2 x) X1)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52232 X0 X1 X2 x x
       have i₂ := eq49683 (M.op X1 (M.op (M.op x (M.op (M.op x x) x)) x))
       grind)
    | exact superpose eq49683 eq52232
    | exact resolve eq52232 eq49683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52232
  have eq52470 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52456 X0 X1 X2
       have i₂ := eq49681 X2
       grind)
    | exact superpose eq49681 eq52456
    | exact resolve eq52456 eq49681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49681 eq52456
  have eq54278 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52470 X0 (σ x) (σ x)
       have i₂ := eq46919
       grind)
    | exact superpose eq46919 eq52470
    | exact resolve eq52470 eq46919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46919 eq52470
  have eq54751 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq54278 X0
       have i₂ := eq50030 X0 (σ x)
       grind)
    | exact superpose eq50030 eq54278
    | exact resolve eq54278 eq50030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54278
  have eq55370 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq50030 X0 (σ x)
       have i₂ := eq54751 X0
       grind)
    | exact superpose eq54751 eq50030
    | exact resolve eq50030 eq54751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50030 eq54751
  have eq56537 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55370 (σ y)
       grind)
    | exact superpose eq55370 eq16
    | exact resolve eq16 eq55370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55370
  have eq57259 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq56537
       have i₂ := eq49683 y
       grind)
    | exact superpose eq49683 eq56537
    | exact resolve eq56537 eq49683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49683 eq56537
  have eq57260 : False := by grind
  exact eq57260

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_y_y_y_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  have eq59 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op X0 y))) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 y) (M.op x y))) := by
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
  have eq63 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
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
  clear eq24
  have eq73 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq74 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq90 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq74 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | (have j0 := eq74 y x
       grind)
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq74
    | (have j0 := eq74 (σ y) (σ x)
       grind)
    | exact resolve eq74 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq442 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq451 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq442 X0
       grind)
    | exact superpose eq442 eq14
    | exact resolve eq14 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq74 (M.op X0 X0) X0
       have i₂ := eq442 X0
       grind)
    | exact superpose eq442 eq74
    | (have j0 := eq74 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq74 (M.op X0 X0) X0
       have r₂ := eq442 X0
       grind)
    | exact resolve eq74 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq458 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq455 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq605 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq95 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq606 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq1343 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq59 eq451
    | exact resolve eq451 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1345 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq60 eq451
    | exact resolve eq451 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq1373 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq1343 eq74
    | (have j0 := eq74 y (M.op x y)
       grind)
    | (have r₁ := eq74 y (M.op x y)
       have r₂ := eq1343
       grind)
    | exact resolve eq74 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1378 : (M.op x y) = (k y (M.op x y)) := by grind
  clear eq1373
  have eq1414 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1378 eq73
    | exact resolve eq73 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1378
  have eq1418 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1414
    | exact resolve eq1414 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1425 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1418 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1426 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1425
  have eq1653 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1426 eq60
    | exact resolve eq60 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1654 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1426 eq63
    | exact resolve eq63 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1426
  have eq1690 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1345 eq1653
    | exact resolve eq1653 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345 eq1653
  have eq5406 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq606 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq606
    | (have j0 := eq606 (τ X0)
       grind)
    | exact resolve eq606 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq606
  have eq5416 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5406 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5406
    | (have j0 := eq5406 X0
       grind)
    | exact resolve eq5406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5406
  have eq5422 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5416 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5416
    | (have j0 := eq5416 X0
       grind)
    | exact resolve eq5416 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5416
  have eq13462 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1690 eq1654
    | exact resolve eq1654 eq1690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654 eq1690
  have eq13514 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq13462
  have eq13515 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13514
    | exact resolve eq13514 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13514
  have eq24469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq24479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq24469
    | exact resolve eq24469 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24469
  have eq24490 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq24479
       have r₂ := eq27
       grind)
    | exact resolve eq24479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24479
  have eq24493 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq24490
    | exact resolve eq24490 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24490
  have eq24650 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq24493 eq458
    | exact resolve eq458 eq24493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq24493
  have eq24745 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq24650 eq84
    | exact resolve eq84 eq24650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq24650
  have eq24803 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq24745
    | exact resolve eq24745 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24745
  have eq24808 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq5422 y
       grind)
    | (have r₁ := eq24803
       have r₂ := eq5422 y
       grind)
    | exact resolve eq24803 eq5422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5422 eq24803
  have eq24986 : ∀ X0 : G, y ≠ y ∨ (k y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq24808
       grind)
    | exact superpose eq24808 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq24808
       grind)
    | exact resolve eq13 eq24808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24808
  have eq25044 : ∀ X0 : G, (k y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq24986 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24986
  have eq25317 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq25044 x
       grind)
    | exact superpose eq25044 eq71
    | exact resolve eq71 eq25044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq25044
  have eq25359 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25317
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25317
    | exact resolve eq25317 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25317
  have eq25393 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25359
       have r₂ := eq91
       grind)
    | exact resolve eq25359 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq25359
  have eq25425 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25393 eq79
    | exact resolve eq79 eq25393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq25393
  have eq25455 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq25425
    | exact resolve eq25425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq25425
  have eq25459 : x = (k y x) := by
    first
    | (have r₁ := eq25455
       have r₂ := eq90
       grind)
    | exact resolve eq25455 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq25455
  have eq25623 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq25459
       grind)
    | exact superpose eq25459 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq25459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25459
  have eq25634 : x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq25623
  have eq25645 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25634
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25634
    | exact resolve eq25634 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25634
  have eq25734 : y = (M.op y (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59 y
       have i₂ := eq25645
       grind)
    | exact superpose eq25645 eq59
    | exact resolve eq59 eq25645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq25735 : x = (M.op x (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62 y
       have i₂ := eq25645
       grind)
    | exact superpose eq25645 eq62
    | exact resolve eq62 eq25645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq25645
  have eq25848 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1343 eq25734
    | exact resolve eq25734 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343 eq25734
  have eq30862 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25848 eq25735
    | exact resolve eq25735 eq25848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25735 eq25848
  have eq30915 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq30862
  have eq30916 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30915
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30915
    | exact resolve eq30915 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq30915
  have eq30917 : x = (M.op x y) := by grind
  clear eq30916
  have eq30920 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30917 eq20
    | exact resolve eq20 eq30917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30917
  have eq31074 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30920
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30920
    | exact resolve eq30920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq30920
  have eq31637 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq31074 eq26
    | exact resolve eq26 eq31074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31637 eq13515
    | exact resolve eq13515 eq31637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13515 eq31637
  have eq31915 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31822
       have r₂ := eq27
       grind)
    | exact resolve eq31822 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31822
  have eq31921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31074 eq31915
    | exact resolve eq31915 eq31074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31074 eq31915
  have eq31923 : False := by grind
  exact eq31923

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_y_pxx_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op X0 y))) = X0 := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (σ (M.op x x)) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq35 (M.op x x)
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq35
    | exact resolve eq35 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : x = (M.op x (M.op (M.op x y) (M.op x y))) := by
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
  have eq185 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op x y) (M.op X0 y))) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq211 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq174
  have eq598 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq598
       grind)
    | exact superpose eq598 eq40
    | exact resolve eq40 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq819 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq818
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq818
    | exact resolve eq818 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq821 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq819
    | exact resolve eq819 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq831 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq185
    | exact resolve eq185 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq850 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op X0 X0)
       have i₂ := eq831 X0
       grind)
    | exact superpose eq831 eq16
    | exact resolve eq16 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq175 eq850
    | exact resolve eq850 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq911 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq176 eq850
    | exact resolve eq850 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq850
  have eq1594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq821 eq602
    | exact resolve eq602 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq1601 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1594
       have r₂ := eq27
       grind)
    | exact resolve eq1594 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1608 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1601 eq200
    | exact resolve eq200 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq1601
  have eq1631 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq1608
    | exact resolve eq1608 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608
  have eq1633 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq1631
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1631 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq1635 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq598
       have i₂ := eq1633
       grind)
    | exact superpose eq1633 eq598
    | exact resolve eq598 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq1636 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq1633
       grind)
    | exact superpose eq1633 eq35
    | exact resolve eq35 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1633
  have eq1638 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1635
  have eq1641 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1636
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1636
    | exact resolve eq1636 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1651 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq831 x
       have i₂ := eq1638
       grind)
    | exact superpose eq1638 eq831
    | exact resolve eq831 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq1667 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1651
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1651
    | exact resolve eq1651 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq1674 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1667 eq189
    | exact resolve eq189 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1688 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1667 eq911
    | exact resolve eq911 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1698 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1688 eq1674
    | exact resolve eq1674 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1702 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1698
    | exact resolve eq1698 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1723 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1702 eq1667
    | exact resolve eq1667 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667 eq1702
  have eq1724 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1723
  have eq1734 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1724 eq31
    | exact resolve eq31 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq1772 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1734
    | exact resolve eq1734 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1734
  have eq1778 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1772
       grind)
    | exact superpose eq1772 eq18
    | exact resolve eq18 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1790 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq908
       have i₂ := eq1772
       grind)
    | exact superpose eq1772 eq908
    | exact resolve eq908 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq1837 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1641 eq602
    | exact resolve eq602 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq1641
  have eq1841 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1837
  have eq1910 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1841 eq831
    | exact resolve eq831 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq1841
  have eq1926 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1910
    | exact resolve eq1910 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910
  have eq1933 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1926 eq189
    | exact resolve eq189 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1947 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1926 eq911
    | exact resolve eq911 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq1926
  have eq1960 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1947 eq1933
    | exact resolve eq1933 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933 eq1947
  have eq1964 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1960
    | exact resolve eq1960 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq1965 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1964
  have eq1968 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1965 eq27
    | exact resolve eq27 eq1965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1965
  have eq2002 : (τ (σ y)) = (k y (τ (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1688 eq211
    | exact resolve eq211 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq1688
  have eq2033 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2002
    | exact resolve eq2002 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2002
  have eq2038 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1772 eq2033
    | exact resolve eq2033 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772 eq2033
  have eq2109 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq657 x x
       have i₂ := eq2038
       grind)
    | exact superpose eq2038 eq657
    | (have j0 := eq657 x x
       grind)
    | (have r₁ := eq657 x x
       have r₂ := eq2038
       grind)
    | exact resolve eq657 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq2110 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2109
  have eq2111 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2110
  have eq2197 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1790 eq184
    | exact resolve eq184 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq1790
  have eq2213 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1778 eq2197
    | exact resolve eq2197 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778 eq2197
  have eq2214 : x = (M.op x y) ∨ x = y := by grind
  clear eq2213
  have eq2221 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq2214
       grind)
    | exact superpose eq2214 eq22
    | exact resolve eq22 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2254 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq2221
    | exact resolve eq2221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2277 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2254 eq1968
    | (have r₁ := eq1968
       have r₂ := eq2254
       grind)
    | exact resolve eq1968 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968 eq2254
  have eq2278 : y = (M.op x y) ∨ x = y := by grind
  clear eq2277
  have eq2307 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq2278
  have eq2309 : x = y := by
    first
    | (have r₁ := eq2307
       have r₂ := eq2214
       grind)
    | exact resolve eq2307 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214 eq2307
  have eq2322 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2309
       grind)
    | exact superpose eq2309 eq18
    | exact resolve eq18 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2323 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2309
       grind)
    | exact superpose eq2309 eq24
    | exact resolve eq24 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2343 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2323
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2323
    | exact resolve eq2323 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2344 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2343 eq26
    | exact resolve eq26 eq2343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2343
  have eq2393 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq181
       have i₂ := eq2322
       grind)
    | exact superpose eq2322 eq181
    | exact resolve eq181 eq2322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2398 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2111
       have i₂ := eq2322
       grind)
    | exact superpose eq2322 eq2111
    | exact resolve eq2111 eq2322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111 eq2322
  have eq2416 : x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2398
  have eq2421 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2416
       have i₂ := eq2309
       grind)
    | exact superpose eq2309 eq2416
    | exact resolve eq2416 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309 eq2416
  have eq2422 : x = (M.op x y) := by grind
  clear eq2421
  have eq2424 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2393
    | exact resolve eq2393 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq2430 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq2422
       grind)
    | exact superpose eq2422 eq22
    | exact resolve eq22 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2422
  have eq2469 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2430 eq20
    | exact resolve eq20 eq2430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2430
  have eq2976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2424 eq657
    | (have j0 := eq657 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq657 (σ x) (σ (M.op x y))
       have r₂ := eq2424
       grind)
    | exact resolve eq657 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq2424
  have eq2977 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq2976
  have eq2978 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2469 eq2977
    | exact resolve eq2977 eq2469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2977
  have eq2983 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2344 eq2978
    | exact resolve eq2978 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978
  have eq2986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2344 eq2983
    | exact resolve eq2983 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344 eq2983
  have eq2988 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2986
       have r₂ := eq27
       grind)
    | exact resolve eq2986 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq2992 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2988 eq27
    | exact resolve eq27 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2988
  have eq3023 : False := by grind
  exact eq3023

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pxx_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 (M.op X0 X1) X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq78
    | exact resolve eq78 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq78
    | exact resolve eq78 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq86 X0 X2
       grind)
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq200 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X0 X0)))) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X1 X2 X0 (M.op X0 X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq62
    | exact resolve eq62 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq401 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 y y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X2 (σ X1)) (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq200 X0 X1
       grind)
    | exact superpose eq200 eq9
    | (have j1 := eq200 X1 X1
       grind)
    | exact resolve eq9 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq200 X0 X0
       grind)
    | exact superpose eq200 eq68
    | (have j1 := eq200 X0 X0
       grind)
    | exact resolve eq68 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq200 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq423 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq425 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq419 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq439 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq423 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq423
    | (have j0 := eq423 (τ X0)
       grind)
    | exact resolve eq423 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq441 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq439 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq439
    | (have j0 := eq439 X0
       grind)
    | exact resolve eq439 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq444 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq441
    | (have j0 := eq441 X0
       grind)
    | exact resolve eq441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq629 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212 X0 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq212
    | exact resolve eq212 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq1503 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq204 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | exact resolve eq204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1572 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1503 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1503
    | (have j0 := eq1503 X1 X1
       grind)
    | exact resolve eq1503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1835 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq425 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq425
    | (have j0 := eq425 (τ X0)
       grind)
    | exact resolve eq425 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq425
  have eq1875 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1835 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1835
    | (have j0 := eq1835 X0
       grind)
    | exact resolve eq1835 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1879 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1875 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1875
    | (have j0 := eq1875 X0
       grind)
    | exact resolve eq1875 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq2021 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (M.op X0 (M.op X2 (k X0 X0)))))) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X2 X1 X0 (k X0 X0)
       have i₂ := eq1879 X0
       grind)
    | exact superpose eq1879 eq61
    | (have j1 := eq1879 X0
       grind)
    | exact resolve eq61 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1879
  have eq3721 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k X0 X1) X2
       have i₂ := eq1572 X0 X1
       grind)
    | exact superpose eq1572 eq28
    | (have j1 := eq1572 X1 X1
       grind)
    | exact resolve eq28 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq3728 : ∀ X0 X1 X2 : G, (k (k X0 X1) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3721 X0 X1 X2
       have i₂ := eq28 (M.op X0 X1) X2
       grind)
    | exact superpose eq28 eq3721
    | (have j0 := eq3721 X1 X1 X2
       grind)
    | exact resolve eq3721 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3721
  have eq4393 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq401
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq401
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq401 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq4396 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq4393
  have eq5520 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (M.op X2 (σ (τ X1))) (σ (τ (k X0 X1))))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq403 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq403
    | (have j0 := eq403 (τ X1) (τ X1) X2
       grind)
    | exact resolve eq403 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq5602 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (M.op X2 (σ (τ X1))) (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5520 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5520
    | (have j0 := eq5520 X1 X1 X2
       grind)
    | exact resolve eq5520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5520
  have eq5611 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (M.op X2 X1) (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5602 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5602
    | (have j0 := eq5602 X1 X1 X2
       grind)
    | exact resolve eq5602 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5602
  have eq5617 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) (k X0 X1))) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5611 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5611
    | (have j0 := eq5611 X1 X1 X2
       grind)
    | exact resolve eq5611 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5611
  have eq5622 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X0 (M.op (M.op X2 X1) (k X0 X1))) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5617 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5617
    | (have j0 := eq5617 X0 X1 X2
       grind)
    | exact resolve eq5617 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5617
  have eq5627 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 (M.op (M.op X2 X1) (k X0 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5622 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5622
    | (have j0 := eq5622 X0 X1 X2
       grind)
    | exact resolve eq5622 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5622
  have eq5632 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) (k X0 X1))) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5627 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5627
    | (have j0 := eq5627 X0 X1 X2
       grind)
    | exact resolve eq5627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5627
  have eq8540 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (k X0 X0))) = (M.op (M.op X1 (M.op X0 (k X0 X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2021 X0 (M.op X1 (M.op X0 (k X0 X0))) X0
       have i₂ := eq9 X0 X1 (M.op X0 (k X0 X0))
       grind)
    | exact superpose eq9 eq2021
    | (have j0 := eq2021 X0 X1 x
       grind)
    | exact resolve eq2021 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq11693 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (M.op X0 (k X0 X1))) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106 (k X0 X1) X0 X1
       have i₂ := eq5632 X0 X1 (k X0 X1)
       grind)
    | exact superpose eq5632 eq106
    | (have j1 := eq5632 X1 X1 x
       grind)
    | exact resolve eq106 eq5632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq5632
  have eq24023 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (M.op X1 X2) X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3728 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3728
    | (have j0 := eq3728 X2 X2 X2
       grind)
    | exact resolve eq3728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728
  have eq33246 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8540 x (k x x)
       have i₂ := eq11693 x x
       grind)
    | exact superpose eq11693 eq8540
    | (have j0 := eq8540 X0 x
       have j1 := eq11693 X0 X0
       grind)
    | exact resolve eq8540 eq11693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8540 eq11693
  have eq33372 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq33246 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33246
  have eq33798 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq206 (k (τ x) (τ x)) x
       have i₂ := eq33372 (τ x)
       grind)
    | exact superpose eq33372 eq206
    | (have j0 := eq206 (τ X0) X0
       have j1 := eq33372 (τ X0)
       grind)
    | exact resolve eq206 eq33372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq33372
  have eq33807 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq33798 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33798
  have eq33827 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq33807 X0
       have j1 := eq444 (τ X0)
       grind)
    | (have r₁ := eq33807 X0
       have r₂ := eq444 (τ X0)
       grind)
    | exact resolve eq33807 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq33807
  have eq33841 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33827 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq33827
    | (have j0 := eq33827 X0
       grind)
    | exact resolve eq33827 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq33827
  have eq33845 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33841 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33841
    | (have j0 := eq33841 X0
       grind)
    | exact resolve eq33841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33841
  have eq34440 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (k (σ X0) (σ X0)) X0
       have i₂ := eq33845 (σ X0)
       grind)
    | exact superpose eq33845 eq22
    | (have j1 := eq33845 (σ X0)
       grind)
    | exact resolve eq22 eq33845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33845
  have eq34487 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq34440 x
       have i₂ := eq22 (σ x) x
       grind)
    | exact superpose eq22 eq34440
    | (have j0 := eq34440 X0
       grind)
    | exact resolve eq34440 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq34440
  have eq34522 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq34487 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34487
    | (have j0 := eq34487 X0
       grind)
    | exact resolve eq34487 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34487
  have eq34553 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34522 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34522
    | (have j0 := eq34522 X0
       grind)
    | exact resolve eq34522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34522
  have eq34613 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24023 X0 X0 X0
       have i₂ := eq34553 X0
       grind)
    | exact superpose eq34553 eq24023
    | (have j0 := eq24023 X0 X0 X0
       have j1 := eq34553 X0
       grind)
    | exact resolve eq24023 eq34553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24023 eq34553
  have eq34698 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq34613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34613
  have eq34820 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 X0) X0
       have i₂ := eq34698 X0
       grind)
    | exact superpose eq34698 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq34698 X0
       grind)
    | exact resolve eq14 eq34698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34698
  have eq34897 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq34820 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34820
  have eq34946 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34897 X0
       have i₂ := eq88 X0 X0
       grind)
    | exact superpose eq88 eq34897
    | (have j0 := eq34897 X0
       grind)
    | exact resolve eq34897 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34897
  have eq34994 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq34946 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq34946 x
       have r₂ := eq12 x x
       grind)
    | (have r₁ := eq34946 x
       have r₂ := eq12 (M.op x x) x
       grind)
    | exact resolve eq34946 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34946
  have eq35001 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34994 X0
       have i₂ := eq88 X0 X0
       grind)
    | exact superpose eq88 eq34994
    | (have j0 := eq34994 X0
       grind)
    | exact resolve eq34994 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34994
  have eq35004 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq35001 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq35001 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq35001 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35001
  have eq35084 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35004 (σ X0)
       grind)
    | exact superpose eq35004 eq15
    | exact resolve eq15 eq35004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35093 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq35004 (τ X0)
       grind)
    | exact superpose eq35004 eq31
    | exact resolve eq31 eq35004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq35154 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35093 X0
       have i₂ := eq35004 X0
       grind)
    | exact superpose eq35004 eq35093
    | exact resolve eq35093 eq35004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35093
  have eq35163 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35084 X0
       have i₂ := eq35004 X0
       grind)
    | exact superpose eq35004 eq35084
    | exact resolve eq35084 eq35004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35004 eq35084
  have eq35277 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (τ X0)
       have i₂ := eq35154 X0
       grind)
    | exact superpose eq35154 eq68
    | exact resolve eq68 eq35154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq35282 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op X1 (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78 (τ X0) X1
       have i₂ := eq35154 X0
       grind)
    | exact superpose eq35154 eq78
    | exact resolve eq78 eq35154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35599 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq35163 X0
       grind)
    | exact superpose eq35163 eq9
    | exact resolve eq9 eq35163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35810 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35277 (σ y)
       have i₂ := eq4396
       grind)
    | exact superpose eq4396 eq35277
    | exact resolve eq35277 eq4396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396 eq35277
  have eq35974 : (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35810
       have i₂ := eq35154 (σ y)
       grind)
    | exact superpose eq35154 eq35810
    | exact resolve eq35810 eq35154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35154 eq35810
  have eq35990 : (τ (σ y)) = (τ (σ (M.op y y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35974
       have i₂ := eq35163 y
       grind)
    | exact superpose eq35163 eq35974
    | exact resolve eq35974 eq35163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35974
  have eq36000 : (M.op y y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35990
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq35990
    | exact resolve eq35990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35990
  have eq36004 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36000
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq36000
    | exact resolve eq36000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36000
  have eq36005 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq36004
  have eq38163 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (σ (M.op X0 X0))) (M.op X1 (σ (σ X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35599 (σ X0) X1
       have i₂ := eq35163 X0
       grind)
    | exact superpose eq35163 eq35599
    | exact resolve eq35599 eq35163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35599
  have eq56004 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88 (σ y) (σ x)
       have i₂ := eq36005
       grind)
    | exact superpose eq36005 eq88
    | exact resolve eq88 eq36005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36005
  have eq56172 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56004
       have i₂ := eq35163 y
       grind)
    | exact superpose eq35163 eq56004
    | exact resolve eq56004 eq35163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35163 eq56004
  have eq56254 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq56172
       grind)
    | exact superpose eq56172 eq10
    | exact resolve eq10 eq56172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56172
  have eq56368 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56254
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq56254
    | exact resolve eq56254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56254
  have eq56369 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq56368
  have eq56393 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq78 y X0
       have i₂ := eq56369
       grind)
    | exact superpose eq56369 eq78
    | exact resolve eq78 eq56369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56562 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq629 y y x
       have i₂ := eq56369
       grind)
    | exact superpose eq56369 eq629
    | exact resolve eq629 eq56369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56369
  have eq56640 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56562 X0
       have i₂ := eq88 y X0
       grind)
    | exact superpose eq88 eq56562
    | exact resolve eq56562 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56562
  have eq57379 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56393 X0
       have i₂ := eq56640 X0
       grind)
    | exact superpose eq56640 eq56393
    | exact resolve eq56393 eq56640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56393 eq56640
  have eq57622 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq57379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57379
  have eq57682 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq88 y x
       have i₂ := eq57622 X0
       grind)
    | exact superpose eq57622 eq88
    | (have j1 := eq57622 y
       grind)
    | exact resolve eq88 eq57622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57622
  have eq57805 : y = (M.op y y) := by
    first
    | (have j0 := eq57682 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57682
  have eq57885 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq78 y X0
       have i₂ := eq57805
       grind)
    | exact superpose eq57805 eq78
    | exact resolve eq78 eq57805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq57928 : ∀ X0 : G, (M.op X0 (M.op (τ y) (M.op X0 (τ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35282 y X0
       have i₂ := eq57805
       grind)
    | exact superpose eq57805 eq35282
    | exact resolve eq35282 eq57805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35282
  have eq58054 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have i₁ := eq629 y y x
       have i₂ := eq57805
       grind)
    | exact superpose eq57805 eq629
    | exact resolve eq629 eq57805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57805
  have eq58133 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq58054 X0
       have i₂ := eq88 y X0
       grind)
    | exact superpose eq88 eq58054
    | exact resolve eq58054 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq58054
  have eq58538 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq57885 X0
       have i₂ := eq58133 X0
       grind)
    | exact superpose eq58133 eq57885
    | exact resolve eq57885 eq58133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57885 eq58133
  have eq58719 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X1 y) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq629 y X1 X0
       have i₂ := eq58538 X0
       grind)
    | exact superpose eq58538 eq629
    | exact resolve eq629 eq58538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq59058 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58719 X0 X0
       have i₂ := eq58538 X0
       grind)
    | exact superpose eq58538 eq58719
    | exact resolve eq58719 eq58538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58719
  have eq64325 : ∀ X0 : G, (M.op X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq57928 X0
       have i₂ := eq59058 X0 (τ y)
       grind)
    | exact superpose eq59058 eq57928
    | exact resolve eq57928 eq59058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57928
  have eq64420 : ∀ X0 : G, (M.op X0 (M.op (σ (σ (τ y))) (M.op X0 (σ (σ (τ y)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq38163 (τ y) X0
       have i₂ := eq64325 (τ y)
       grind)
    | exact superpose eq64325 eq38163
    | exact resolve eq38163 eq64325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38163 eq64325
  have eq64876 : ∀ X0 : G, (M.op X0 (σ (σ (τ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq64420 X0
       have i₂ := eq59058 X0 (σ (σ (τ y)))
       grind)
    | exact superpose eq59058 eq64420
    | exact resolve eq64420 eq59058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59058 eq64420
  have eq64981 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq64876 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq64876
    | exact resolve eq64876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64876
  have eq65737 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64981 (σ x)
       grind)
    | exact superpose eq64981 eq16
    | exact resolve eq16 eq64981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64981
  have eq65751 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq65737
       have i₂ := eq58538 x
       grind)
    | exact superpose eq58538 eq65737
    | exact resolve eq65737 eq58538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58538 eq65737
  have eq65752 : False := by grind
  exact eq65752

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyy_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq14 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq43
    | (have j0 := eq43 (σ X0) (σ X1)
       grind)
    | exact resolve eq43 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq43 (τ X0) X1
       grind)
    | exact superpose eq43 eq18
    | (have j1 := eq43 (τ X0) X1
       grind)
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq77 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq84 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op (M.op X2 (M.op (M.op X0 X1) X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X0 X1) (M.op X2 (M.op (M.op X0 X1) X1)) X0 X1
       have i₂ := eq9 (M.op X0 X1) X2 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq138 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56 x y
       grind)
    | exact superpose eq56 eq16
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq16 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq200 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq301 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq333 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq301
    | (have j0 := eq301 X0 X1
       grind)
    | exact resolve eq301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq138
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq138
    | (have j1 := eq43 (σ x) (σ y)
       grind)
    | exact resolve eq138 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq410 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq407
  have eq414 : y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq84 y
       have i₂ := eq410
       grind)
    | exact superpose eq410 eq84
    | exact resolve eq84 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq416 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 y))) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq410
       grind)
    | exact superpose eq410 eq9
    | exact resolve eq9 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 y
       have i₂ := eq410
       grind)
    | exact superpose eq410 eq9
    | exact resolve eq9 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 : G, (M.op X0 (M.op y (M.op X0 x))) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq414
       grind)
    | exact superpose eq414 eq9
    | exact resolve eq9 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq2644 : y = (M.op y (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq416 y
       have i₂ := eq410
       grind)
    | exact superpose eq410 eq416
    | exact resolve eq416 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq2686 : y = (M.op y (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2644
  have eq3040 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq522 x
       have i₂ := eq2686
       grind)
    | exact superpose eq2686 eq522
    | exact resolve eq522 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686
  have eq3041 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq522 (M.op X0 y)
       have i₂ := eq417 X0
       grind)
    | exact superpose eq417 eq522
    | exact resolve eq522 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq522
  have eq3081 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op X0 y) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3041 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041
  have eq3082 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3040
  have eq3529 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k (M.op y y) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq200 y
       have i₂ := eq3081 y
       grind)
    | exact superpose eq3081 eq200
    | (have j0 := eq200 y
       grind)
    | (have r₁ := eq200 y
       have r₂ := eq3081 y
       grind)
    | exact resolve eq200 eq3081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081
  have eq3573 : (M.op y y) = (k (M.op y y) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3529
  have eq3811 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3573
       have i₂ := eq410
       grind)
    | exact superpose eq410 eq3573
    | exact resolve eq3573 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq3573
  have eq3822 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3811
  have eq3975 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq138
       have i₂ := eq3822
       grind)
    | exact superpose eq3822 eq138
    | exact resolve eq138 eq3822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq3822
  have eq3997 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3975
  have eq4132 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3997
       have i₂ := eq3082
       grind)
    | exact superpose eq3082 eq3997
    | exact resolve eq3997 eq3082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082 eq3997
  have eq4133 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4132
  have eq4134 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4133
  have eq4295 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq4134
       grind)
    | exact superpose eq4134 eq9
    | exact resolve eq9 eq4134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4665 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (M.op X0 (σ y))))) = (M.op (M.op X1 (M.op X0 (M.op (σ x) (M.op X0 (σ y))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (M.op (σ x) (M.op X0 (σ y))) x
       have i₂ := eq4295 X0
       grind)
    | exact superpose eq4295 eq86
    | exact resolve eq86 eq4295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq4695 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4665 X0 X1
       have i₂ := eq4295 X0
       grind)
    | exact superpose eq4295 eq4665
    | exact resolve eq4665 eq4295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4295 eq4665
  have eq4839 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4695 (σ y) (σ y)
       have i₂ := eq4134
       grind)
    | exact superpose eq4134 eq4695
    | exact resolve eq4695 eq4134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4845 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq200 X0
       have i₂ := eq4695 X0 X0
       grind)
    | exact superpose eq4695 eq200
    | (have j0 := eq200 X0
       grind)
    | (have r₁ := eq200 X0
       have r₂ := eq4695 X0 X0
       grind)
    | exact resolve eq200 eq4695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq4950 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq4845 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4845
  have eq4994 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4839
       grind)
    | exact superpose eq4839 eq16
    | exact resolve eq16 eq4839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4839
  have eq5091 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4950 (σ y)
       have i₂ := eq4134
       grind)
    | exact superpose eq4134 eq4950
    | exact resolve eq4950 eq4134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4134 eq4950
  have eq5112 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq5091
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5091
    | exact resolve eq5091 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091
  have eq5265 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq333 x y
       have i₂ := eq5112
       grind)
    | exact superpose eq5112 eq333
    | (have j0 := eq333 x y
       grind)
    | exact resolve eq333 eq5112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq5112
  have eq5307 : x = (M.op y y) := by
    first
    | (have r₁ := eq5265
       have r₂ := eq4994
       grind)
    | exact resolve eq5265 eq4994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5265
  have eq5661 : x = (M.op x y) := by
    first
    | (have i₁ := eq4695 y y
       have i₂ := eq5307
       grind)
    | exact superpose eq5307 eq4695
    | exact resolve eq4695 eq5307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4695 eq5307
  have eq5972 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4994
       have i₂ := eq5661
       grind)
    | exact superpose eq5661 eq4994
    | exact resolve eq4994 eq5661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994 eq5661
  have eq6031 : False := by grind
  exact eq6031
