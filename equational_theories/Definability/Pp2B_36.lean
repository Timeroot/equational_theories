import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pyx_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq212 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op sF0 (M.op x X0)) x)
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op sF4 (M.op x X0)) x)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq483 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq491 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X1) X1 X0
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq482 eq57
    | exact resolve eq57 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq527 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq483 eq57
    | exact resolve eq57 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq673 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X1 (M.op X1 X0) x
       have i₂ := eq56 X1 X1 X0 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq678 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) X3 X1
       have i₂ := eq56 X3 X1 X0 X2
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq917 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq70
  have eq1126 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ X0)) = (σ (M.op y y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq917 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq917
    | (have j0 := eq917 y X0
       grind)
    | exact resolve eq917 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq1150 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ X0)) = (σ (M.op y y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1126 X0
       have i₂ := eq676 (σ X0) sF3
       grind)
    | (have i₁ := eq1126 X0
       have i₂ := eq676 sF3 (σ X0)
       grind)
    | exact superpose eq676 eq1126
    | (have j0 := eq1126 X0
       grind)
    | exact resolve eq1126 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1168 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1150 X0
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq1150
    | (have j0 := eq1150 X0
       grind)
    | exact resolve eq1150 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1150
  have eq1537 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq676 (M.op X1 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq676 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq676 eq481
    | exact resolve eq481 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1642 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq676 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq676 X0 (M.op X1 X2)
       grind)
    | exact superpose eq676 eq491
    | exact resolve eq491 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1921 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq673 X0 X1 X2
       have i₂ := eq676 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | (have i₁ := eq673 X0 X1 X2
       have i₂ := eq676 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq676 eq673
    | exact resolve eq673 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq2170 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1921 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1537 X2 X1 X0
       grind)
    | exact superpose eq1537 eq1921
    | exact resolve eq1921 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq1921
  have eq2289 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq676 (M.op sF0 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq212 X0 X0
       have i₂ := eq676 X0 (M.op sF0 (M.op X0 X0))
       grind)
    | exact superpose eq676 eq212
    | exact resolve eq212 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2316 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq676 (M.op sF4 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq217 X0 X0
       have i₂ := eq676 X0 (M.op sF4 (M.op X0 X0))
       grind)
    | exact superpose eq676 eq217
    | exact resolve eq217 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq676
  have eq3847 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op (M.op x y) (M.op X0 X1))) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq2289 eq57
    | exact resolve eq57 eq2289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2289
  have eq3880 : ∀ X0 X1 : G, x = (M.op (M.op X1 y) (M.op (M.op (M.op x y) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3847 x X1
       have i₂ := eq1642 (M.op X1 y) (M.op sF0 (M.op x X1)) x
       grind)
    | exact superpose eq1642 eq3847
    | exact resolve eq3847 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3847
  have eq3956 : ∀ X0 X1 : G, x = (M.op (M.op X1 y) (M.op X0 (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3880 X0 X1
       have i₂ := eq2170 X0 (M.op X1 y) (M.op sF0 (M.op X0 X1))
       grind)
    | (have i₁ := eq3880 x X1
       have i₂ := eq2170 (M.op sF0 (M.op x X1)) (M.op X1 y) x
       grind)
    | exact superpose eq2170 eq3880
    | exact resolve eq3880 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880
  have eq4556 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2316 eq57
    | exact resolve eq57 eq2316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2316
  have eq4593 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4556 x X1
       have i₂ := eq1642 (M.op X1 sF3) (M.op sF4 (M.op x X1)) x
       grind)
    | exact superpose eq1642 eq4556
    | exact resolve eq4556 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556
  have eq4675 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (σ y)) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4593 X0 X1
       have i₂ := eq2170 X0 (M.op X1 sF3) (M.op sF4 (M.op X0 X1))
       grind)
    | (have i₁ := eq4593 x X1
       have i₂ := eq2170 (M.op sF4 (M.op x X1)) (M.op X1 sF3) x
       grind)
    | exact superpose eq2170 eq4593
    | exact resolve eq4593 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4593
  have eq12362 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3))) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq678 X0 X1 X2 X3
       have i₂ := eq491 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq678 X0 X1 X2 X3
       have i₂ := eq491 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq491 eq678
    | exact resolve eq678 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq678
  have eq12363 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12362 X0 X1 X2 X3
       have i₂ := eq1642 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3)) X2
       grind)
    | exact superpose eq1642 eq12362
    | exact resolve eq12362 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642 eq12362
  have eq12364 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12363 X0 X1 X2 X3
       have i₂ := eq2170 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq12363 X0 X1 X2 X3
       have i₂ := eq2170 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq2170 eq12363
    | exact resolve eq12363 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170 eq12363
  have eq97086 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1168 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1168
    | (have j0 := eq1168 x
       grind)
    | exact resolve eq1168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq97285 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97086
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq97086
    | exact resolve eq97086 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq97086
  have eq97322 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq527 eq97285
    | exact resolve eq97285 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97285
  have eq97335 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq527 eq97322
    | exact resolve eq97322 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq97322
  have eq193942 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq507
       grind)
    | exact superpose eq507 eq104
    | exact resolve eq104 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq507
  have eq193954 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq193942 eq97335
    | exact resolve eq97335 eq193942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97335 eq193942
  have eq193973 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq193954
       have r₂ := eq28
       grind)
    | exact resolve eq193954 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193954
  have eq194114 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq193973 eq12364
    | exact resolve eq12364 eq193973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193973
  have eq194267 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq4675 eq194114
    | exact resolve eq194114 eq4675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675 eq194114
  have eq194268 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq194267
  have eq194559 : ∀ X0 X1 : G, y = (M.op (M.op X0 y) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12364 y y X1 X0
       have i₂ := eq194268
       grind)
    | exact superpose eq194268 eq12364
    | exact resolve eq12364 eq194268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12364 eq194268
  have eq194712 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3956 eq194559
    | exact resolve eq194559 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956 eq194559
  have eq194713 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq194712
  have eq197614 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq194713 eq30
    | exact resolve eq30 eq194713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq194713
  have eq197821 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq197614
    | exact resolve eq197614 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq197614
  have eq197822 : x = y := by grind
  clear eq197821
  have eq197844 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq197822
       grind)
    | exact superpose eq197822 eq19
    | exact resolve eq19 eq197822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq197845 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq197822
       grind)
    | exact superpose eq197822 eq25
    | exact resolve eq25 eq197822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq197822
  have eq198050 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq197845
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq197845
    | exact resolve eq197845 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq197845
  have eq198087 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq198050 eq27
    | exact resolve eq27 eq198050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq198050
  have eq198886 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq198087 eq69
    | exact resolve eq69 eq198087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq198087
  have eq199242 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq198886
       have i₂ := eq197844
       grind)
    | exact superpose eq197844 eq198886
    | exact resolve eq198886 eq197844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197844 eq198886
  have eq202359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199242 eq15
    | exact resolve eq15 eq199242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199242
  have eq202435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq202359
    | exact resolve eq202359 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq202359
  have eq202456 : False := by grind
  exact eq202456

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pxy_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq78
    | exact resolve eq78 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq478 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq479 eq57
    | exact resolve eq57 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq479
  have eq584 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X0 (M.op X4 X3)) X4))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X0 (M.op X4 X3)) X4)) X1
       have i₂ := eq55 X3 (M.op X1 X2) X0 X4
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) X1) (M.op (M.op X0 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op sF0 X0) (M.op (M.op X2 (M.op x X0)) x))
       have i₂ := eq55 X0 sF0 X2 x
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq588 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op (M.op X0 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op sF4 X0) (M.op (M.op X2 (M.op x X0)) x))
       have i₂ := eq55 X0 sF4 X2 x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq671 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X0 (M.op X0 X1) x
       have i₂ := eq56 X0 X0 X1 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq926 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq75
  have eq1113 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq926 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq926
    | (have j0 := eq926 x X0
       grind)
    | exact resolve eq926 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq1164 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1113 X0
       have i₂ := eq674 sF2 (σ X0)
       grind)
    | (have i₁ := eq1113 X0
       have i₂ := eq674 (σ X0) sF2
       grind)
    | exact superpose eq674 eq1113
    | (have j0 := eq1113 X0
       grind)
    | exact resolve eq1113 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1178 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1164 X0
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq1164
    | (have j0 := eq1164 X0
       grind)
    | exact resolve eq1164 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1164
  have eq1540 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq478 X0 X1 X2
       have i₂ := eq674 X0 (M.op X1 (M.op X2 X0))
       grind)
    | (have i₁ := eq478 X0 X1 X2
       have i₂ := eq674 (M.op X1 (M.op X2 X0)) X0
       grind)
    | exact superpose eq674 eq478
    | exact resolve eq478 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq1927 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq671 X0 X1 X2
       have i₂ := eq674 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | (have i₁ := eq671 X0 X1 X2
       have i₂ := eq674 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | exact superpose eq674 eq671
    | exact resolve eq671 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq674
  have eq2173 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1927 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1540 X2 X1 X0
       grind)
    | exact superpose eq1540 eq1927
    | exact resolve eq1927 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540 eq1927
  have eq21366 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq586 X0 X1 X0
       have i₂ := eq2173 X0 (M.op sF0 X1) (M.op X0 (M.op X0 X1))
       grind)
    | (have i₁ := eq586 X0 X1 X2
       have i₂ := eq2173 (M.op X0 (M.op X2 X1)) (M.op sF0 X1) X2
       grind)
    | exact superpose eq2173 eq586
    | exact resolve eq586 eq2173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq21432 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq588 X0 X1 X0
       have i₂ := eq2173 X0 (M.op sF4 X1) (M.op X0 (M.op X0 X1))
       grind)
    | (have i₁ := eq588 X0 X1 X2
       have i₂ := eq2173 (M.op X0 (M.op X2 X1)) (M.op sF4 X1) X2
       grind)
    | exact superpose eq2173 eq588
    | exact resolve eq588 eq2173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq37298 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) X3) (M.op X4 (M.op X0 (M.op X4 X3))))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq584 X0 X1 X2 X3 X4
       have i₂ := eq2173 X4 (M.op (M.op X1 X2) X3) (M.op X0 (M.op X4 X3))
       grind)
    | (have i₁ := eq584 X0 X1 X2 X3 X4
       have i₂ := eq2173 (M.op X0 (M.op X4 X3)) (M.op (M.op X1 X2) X3) X4
       grind)
    | exact superpose eq2173 eq584
    | exact resolve eq584 eq2173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq2173
  have eq98653 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1178 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1178
    | (have j0 := eq1178 y
       grind)
    | exact resolve eq1178 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq98847 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98653
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq98653
    | exact resolve eq98653 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq98653
  have eq98882 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq98847
    | exact resolve eq98847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98847
  have eq98894 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq98882
    | exact resolve eq98882 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98882
  have eq193528 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq85
       have i₂ := eq503
       grind)
    | exact superpose eq503 eq85
    | exact resolve eq85 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq503
  have eq193540 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq193528 eq98894
    | exact resolve eq98894 eq193528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98894 eq193528
  have eq193559 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq193540
       have r₂ := eq28
       grind)
    | exact resolve eq193540 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193540
  have eq193737 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq193559 eq37298
    | exact resolve eq37298 eq193559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193559
  have eq193823 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21432 eq193737
    | exact resolve eq193737 eq21432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21432 eq193737
  have eq193824 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq193823
  have eq194176 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) (M.op (M.op (M.op x y) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37298 X0 x x X1 X2
       have i₂ := eq193824
       grind)
    | exact superpose eq193824 eq37298
    | exact resolve eq37298 eq193824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37298 eq193824
  have eq194262 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21366 eq194176
    | exact resolve eq194176 eq21366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21366 eq194176
  have eq194263 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq194262
  have eq194891 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq194263 eq30
    | exact resolve eq30 eq194263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq194263
  have eq195098 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq194891
    | exact resolve eq194891 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq194891
  have eq195099 : x = y := by grind
  clear eq195098
  have eq195121 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq195099
       grind)
    | exact superpose eq195099 eq19
    | exact resolve eq19 eq195099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq195122 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq195099
       grind)
    | exact superpose eq195099 eq25
    | exact resolve eq25 eq195099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq195099
  have eq195327 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq195122
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq195122
    | exact resolve eq195122 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq195122
  have eq195364 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq195327 eq27
    | exact resolve eq27 eq195327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq195327
  have eq199288 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq195364 eq69
    | exact resolve eq69 eq195364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq195364
  have eq199648 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq199288
       have i₂ := eq195121
       grind)
    | exact superpose eq195121 eq199288
    | exact resolve eq199288 eq195121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195121 eq199288
  have eq199784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199648 eq15
    | exact resolve eq15 eq199648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199648
  have eq199860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq199784
    | exact resolve eq199784 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq199784
  have eq199881 : False := by grind
  exact eq199881

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxy_pxx_pxy_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq216 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (σ y) = (M.op (M.op y (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x)) := by
    first
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq480 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq489 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X1) X1 X0
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X1 (M.op X1 X0) x
       have i₂ := eq56 X1 X1 X0 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq731 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq480 X0
       have i₂ := eq675 (M.op X0 sF0) y
       grind)
    | (have i₁ := eq480 X0
       have i₂ := eq675 y (M.op X0 sF0)
       grind)
    | exact superpose eq675 eq480
    | exact resolve eq480 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq1460 : (σ y) = (M.op (M.op y (σ x)) (M.op x (M.op (M.op (σ x) (σ y)) (M.op x y)))) := by
    first
    | (have i₁ := eq218
       have i₂ := eq675 (M.op sF4 sF0) x
       grind)
    | (have i₁ := eq218
       have i₂ := eq675 x (M.op sF4 sF0)
       grind)
    | exact superpose eq675 eq218
    | exact resolve eq218 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1461 : (σ y) = (M.op (M.op y (σ x)) (M.op x (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq1460
       have i₂ := eq675 sF4 sF0
       grind)
    | (have i₁ := eq1460
       have i₂ := eq675 sF0 sF4
       grind)
    | exact superpose eq675 eq1460
    | exact resolve eq1460 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1935 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq672 X0 X1 X2
       have i₂ := eq675 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | (have i₁ := eq672 X0 X1 X2
       have i₂ := eq675 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq675 eq672
    | exact resolve eq672 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq1937 : (σ x) = (M.op (M.op x (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (σ y))) := by
    first
    | exact superpose eq1461 eq57
    | exact resolve eq57 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1461
  have eq1955 : (σ x) = (M.op (M.op y (σ y)) (M.op x (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq1937
       have i₂ := eq675 (M.op x (M.op sF0 sF4)) (M.op y sF3)
       grind)
    | (have i₁ := eq1937
       have i₂ := eq675 (M.op y sF3) (M.op x (M.op sF0 sF4))
       grind)
    | exact superpose eq675 eq1937
    | exact resolve eq1937 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq2317 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op (M.op (M.op x y) (M.op X0 X1)) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq489 sF0 x (M.op X0 X1)
       grind)
    | (have i₁ := eq216 X0 X1
       have i₂ := eq489 (M.op X0 X1) x sF0
       grind)
    | exact superpose eq489 eq216
    | exact resolve eq216 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq489
  have eq2318 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op x (M.op (M.op x y) (M.op X0 X1)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2317 X0 X1
       have i₂ := eq675 (M.op sF0 (M.op X0 X1)) x
       grind)
    | (have i₁ := eq2317 X0 X1
       have i₂ := eq675 x (M.op sF0 (M.op X0 X1))
       grind)
    | exact superpose eq675 eq2317
    | exact resolve eq2317 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq2317
  have eq30894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq30895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq30894
    | exact resolve eq30894 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30894
  have eq30906 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq30895
       have r₂ := eq28
       grind)
    | exact resolve eq30895 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30895
  have eq30910 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq30906
    | exact resolve eq30906 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30906
  have eq31648 : (σ y) = (M.op (M.op y (σ y)) (M.op x (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30910 eq2318
    | exact resolve eq2318 eq30910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318 eq30910
  have eq31710 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq1955 eq31648
    | exact resolve eq31648 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955 eq31648
  have eq31711 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31710
  have eq31791 : ∀ X0 : G, y = (M.op X0 (M.op y (M.op X0 (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1935 X0 y y
       have i₂ := eq31711
       grind)
    | exact superpose eq31711 eq1935
    | exact resolve eq1935 eq31711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935 eq31711
  have eq31858 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq731 eq31791
    | exact resolve eq31791 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq31791
  have eq31859 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq31858
  have eq31919 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq31859 eq30
    | exact resolve eq30 eq31859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31859
  have eq32051 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq31919
    | exact resolve eq31919 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31919
  have eq32052 : x = y := by grind
  clear eq32051
  have eq32072 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32052
       grind)
    | exact superpose eq32052 eq19
    | exact resolve eq19 eq32052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32073 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32052
       grind)
    | exact superpose eq32052 eq25
    | exact resolve eq25 eq32052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32052
  have eq32210 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32073
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32073
    | exact resolve eq32073 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32073
  have eq32227 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32210 eq27
    | exact resolve eq27 eq32210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32210
  have eq32565 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32227 eq69
    | exact resolve eq69 eq32227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq32227
  have eq32691 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32565
       have i₂ := eq32072
       grind)
    | exact superpose eq32072 eq32565
    | exact resolve eq32565 eq32072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32072 eq32565
  have eq32726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32691 eq15
    | exact resolve eq15 eq32691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32691
  have eq32768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq32726
    | exact resolve eq32726 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq32726
  have eq32777 : False := by grind
  exact eq32777

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pxy_pyx_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq212 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op sF0 (M.op x X0)) x)
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq217 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op sF4 (M.op x X0)) x)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq481 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X1) X1 X0
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X0 (M.op X0 X1) x
       have i₂ := eq56 X0 X0 X1 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq678 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) X3 X1
       have i₂ := eq56 X3 X1 X0 X2
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq1620 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq676 X0 (M.op X1 (M.op X2 X0))
       grind)
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq676 (M.op X1 (M.op X2 X0)) X0
       grind)
    | exact superpose eq676 eq481
    | exact resolve eq481 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1651 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq676 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq676 (M.op X1 X2) X0
       grind)
    | exact superpose eq676 eq491
    | exact resolve eq491 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1930 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq673 X0 X1 X2
       have i₂ := eq676 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | (have i₁ := eq673 X0 X1 X2
       have i₂ := eq676 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | exact superpose eq676 eq673
    | exact resolve eq673 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq2185 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1930 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1620 X2 X1 X0
       grind)
    | exact superpose eq1620 eq1930
    | exact resolve eq1930 eq1620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620 eq1930
  have eq2310 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X0
       have i₂ := eq676 X0 (M.op sF0 (M.op X0 X0))
       grind)
    | (have i₁ := eq212 X0 X1
       have i₂ := eq676 (M.op sF0 (M.op X1 X0)) X1
       grind)
    | exact superpose eq676 eq212
    | exact resolve eq212 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2506 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X0
       have i₂ := eq676 X0 (M.op sF4 (M.op X0 X0))
       grind)
    | (have i₁ := eq217 X0 X1
       have i₂ := eq676 (M.op sF4 (M.op X1 X0)) X1
       grind)
    | exact superpose eq676 eq217
    | exact resolve eq217 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq676
  have eq12040 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3))) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq678 X0 X1 X2 X3
       have i₂ := eq491 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq678 X0 X1 X2 X3
       have i₂ := eq491 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq491 eq678
    | exact resolve eq678 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq678
  have eq12041 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12040 X0 X1 X2 X3
       have i₂ := eq1651 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3)) X2
       grind)
    | exact superpose eq1651 eq12040
    | exact resolve eq12040 eq1651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651 eq12040
  have eq12042 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12041 X0 X1 X2 X3
       have i₂ := eq2185 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq12041 X0 X1 X2 X3
       have i₂ := eq2185 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq2185 eq12041
    | exact resolve eq12041 eq2185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185 eq12041
  have eq30646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq30647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq30646
    | exact resolve eq30646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30646
  have eq30658 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq30647
       have r₂ := eq28
       grind)
    | exact resolve eq30647 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30647
  have eq30663 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq30658
    | exact resolve eq30658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30658
  have eq31416 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq30663 eq12042
    | exact resolve eq12042 eq30663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30663
  have eq31449 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq2506 eq31416
    | exact resolve eq31416 eq2506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506 eq31416
  have eq31450 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31449
  have eq31551 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12042 x x X1 X0
       have i₂ := eq31450
       grind)
    | exact superpose eq31450 eq12042
    | exact resolve eq12042 eq31450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12042 eq31450
  have eq31584 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2310 eq31551
    | exact resolve eq31551 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310 eq31551
  have eq31585 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq31584
  have eq31645 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq31585 eq30
    | exact resolve eq30 eq31585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31585
  have eq31781 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq31645
    | exact resolve eq31645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31645
  have eq31782 : x = y := by grind
  clear eq31781
  have eq31804 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq31782
       grind)
    | exact superpose eq31782 eq19
    | exact resolve eq19 eq31782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq31805 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq31782
       grind)
    | exact superpose eq31782 eq25
    | exact resolve eq25 eq31782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq31782
  have eq31942 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31805
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31805
    | exact resolve eq31805 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq31805
  have eq31959 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31942 eq27
    | exact resolve eq27 eq31942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq31942
  have eq32303 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31959 eq69
    | exact resolve eq69 eq31959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq31959
  have eq32428 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32303
       have i₂ := eq31804
       grind)
    | exact superpose eq31804 eq32303
    | exact resolve eq32303 eq31804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31804 eq32303
  have eq32462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32428 eq15
    | exact resolve eq15 eq32428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32428
  have eq32504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq32462
    | exact resolve eq32462 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq32462
  have eq32513 : False := by grind
  exact eq32513

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pxy_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
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
  clear eq37
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq92
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq96
  have eq212 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op sF0 (M.op x X0)) x)
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op sF4 (M.op x X0)) x)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq483 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq491 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X1) X1 X0
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq482 eq57
    | exact resolve eq57 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq527 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq483 eq57
    | exact resolve eq57 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq673 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X1 (M.op X1 X0) x
       have i₂ := eq56 X1 X1 X0 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq678 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) X3 X1
       have i₂ := eq56 X3 X1 X0 X2
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq917 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq70
  have eq1126 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ X0)) = (σ (M.op y y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq917 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq917
    | (have j0 := eq917 X0 y
       grind)
    | exact resolve eq917 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq1150 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ X0)) = (σ (M.op y y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1126 X0
       have i₂ := eq676 (σ X0) sF3
       grind)
    | (have i₁ := eq1126 X0
       have i₂ := eq676 sF3 (σ X0)
       grind)
    | exact superpose eq676 eq1126
    | (have j0 := eq1126 X0
       grind)
    | exact resolve eq1126 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1168 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1150 X0
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq1150
    | (have j0 := eq1150 X0
       grind)
    | exact resolve eq1150 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1150
  have eq1537 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq676 (M.op X1 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq676 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq676 eq481
    | exact resolve eq481 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1642 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq676 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq676 X0 (M.op X1 X2)
       grind)
    | exact superpose eq676 eq491
    | exact resolve eq491 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1921 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq673 X0 X1 X2
       have i₂ := eq676 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | (have i₁ := eq673 X0 X1 X2
       have i₂ := eq676 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq676 eq673
    | exact resolve eq673 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq2170 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1921 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1537 X2 X1 X0
       grind)
    | exact superpose eq1537 eq1921
    | exact resolve eq1921 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq1921
  have eq2289 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq676 (M.op sF0 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq212 X0 X0
       have i₂ := eq676 X0 (M.op sF0 (M.op X0 X0))
       grind)
    | exact superpose eq676 eq212
    | exact resolve eq212 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2316 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq676 (M.op sF4 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq217 X0 X0
       have i₂ := eq676 X0 (M.op sF4 (M.op X0 X0))
       grind)
    | exact superpose eq676 eq217
    | exact resolve eq217 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq676
  have eq3847 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op (M.op x y) (M.op X0 X1))) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq2289 eq57
    | exact resolve eq57 eq2289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2289
  have eq3880 : ∀ X0 X1 : G, x = (M.op (M.op X1 y) (M.op (M.op (M.op x y) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3847 x X1
       have i₂ := eq1642 (M.op X1 y) (M.op sF0 (M.op x X1)) x
       grind)
    | exact superpose eq1642 eq3847
    | exact resolve eq3847 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3847
  have eq3956 : ∀ X0 X1 : G, x = (M.op (M.op X1 y) (M.op X0 (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3880 X0 X1
       have i₂ := eq2170 X0 (M.op X1 y) (M.op sF0 (M.op X0 X1))
       grind)
    | (have i₁ := eq3880 x X1
       have i₂ := eq2170 (M.op sF0 (M.op x X1)) (M.op X1 y) x
       grind)
    | exact superpose eq2170 eq3880
    | exact resolve eq3880 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880
  have eq4556 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2316 eq57
    | exact resolve eq57 eq2316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2316
  have eq4593 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4556 x X1
       have i₂ := eq1642 (M.op X1 sF3) (M.op sF4 (M.op x X1)) x
       grind)
    | exact superpose eq1642 eq4556
    | exact resolve eq4556 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556
  have eq4675 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (σ y)) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4593 X0 X1
       have i₂ := eq2170 X0 (M.op X1 sF3) (M.op sF4 (M.op X0 X1))
       grind)
    | (have i₁ := eq4593 x X1
       have i₂ := eq2170 (M.op sF4 (M.op x X1)) (M.op X1 sF3) x
       grind)
    | exact superpose eq2170 eq4593
    | exact resolve eq4593 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4593
  have eq12362 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3))) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq678 X0 X1 X2 X3
       have i₂ := eq491 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq678 X0 X1 X2 X3
       have i₂ := eq491 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq491 eq678
    | exact resolve eq678 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq678
  have eq12363 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12362 X0 X1 X2 X3
       have i₂ := eq1642 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3)) X2
       grind)
    | exact superpose eq1642 eq12362
    | exact resolve eq12362 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642 eq12362
  have eq12364 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12363 X0 X1 X2 X3
       have i₂ := eq2170 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq12363 X0 X1 X2 X3
       have i₂ := eq2170 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq2170 eq12363
    | exact resolve eq12363 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170 eq12363
  have eq97088 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1168 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1168
    | (have j0 := eq1168 x
       grind)
    | exact resolve eq1168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq97287 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq527 eq97088
    | exact resolve eq97088 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97088
  have eq97324 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97287
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq97287
    | exact resolve eq97287 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq97287
  have eq97338 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq527 eq97324
    | exact resolve eq97324 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq97324
  have eq193997 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq507
       grind)
    | exact superpose eq507 eq77
    | exact resolve eq77 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq507
  have eq194009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq193997 eq97338
    | exact resolve eq97338 eq193997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97338 eq193997
  have eq194028 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq194009
       have r₂ := eq28
       grind)
    | exact resolve eq194009 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194009
  have eq194169 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq194028 eq12364
    | exact resolve eq12364 eq194028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194028
  have eq194322 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq4675 eq194169
    | exact resolve eq194169 eq4675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675 eq194169
  have eq194323 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq194322
  have eq194614 : ∀ X0 X1 : G, y = (M.op (M.op X0 y) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12364 y y X1 X0
       have i₂ := eq194323
       grind)
    | exact superpose eq194323 eq12364
    | exact resolve eq12364 eq194323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12364 eq194323
  have eq194767 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3956 eq194614
    | exact resolve eq194614 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956 eq194614
  have eq194768 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq194767
  have eq197669 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq194768 eq30
    | exact resolve eq30 eq194768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq194768
  have eq197876 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq197669
    | exact resolve eq197669 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq197669
  have eq197877 : x = y := by grind
  clear eq197876
  have eq197899 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq197877
       grind)
    | exact superpose eq197877 eq19
    | exact resolve eq19 eq197877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq197900 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq197877
       grind)
    | exact superpose eq197877 eq25
    | exact resolve eq25 eq197877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq197877
  have eq198105 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq197900
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq197900
    | exact resolve eq197900 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq197900
  have eq198142 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq198105 eq27
    | exact resolve eq27 eq198105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq198105
  have eq198941 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq198142 eq69
    | exact resolve eq69 eq198142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq198142
  have eq199297 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq198941
       have i₂ := eq197899
       grind)
    | exact superpose eq197899 eq198941
    | exact resolve eq198941 eq197899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197899 eq198941
  have eq202414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199297 eq15
    | exact resolve eq15 eq199297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199297
  have eq202490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq202414
    | exact resolve eq202414 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq202414
  have eq202511 : False := by grind
  exact eq202511

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_y_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq57 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq61 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq74 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq122 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq140 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq160 : (σ (k (k y x) x)) = (k (k (σ y) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq39
    | exact resolve eq39 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq270 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq293 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq122 eq16
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq582 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq92 X0 X0
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq92 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq92 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq589 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq588 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq591 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq595 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq591 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq591 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq591 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq893 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq595 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq595
    | (have j0 := eq595 (τ X0) X1
       grind)
    | exact resolve eq595 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq910 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq893 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq893
    | (have j0 := eq893 X0 X1
       grind)
    | exact resolve eq893 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq917 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq910 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq910
    | (have j0 := eq910 X0 X1
       grind)
    | exact resolve eq910 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq3467 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq589 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq589
    | (have j0 := eq589 (τ X0)
       grind)
    | exact resolve eq589 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3468 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq589 x
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq589
    | (have j0 := eq589 x
       grind)
    | exact resolve eq589 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq3491 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3468
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3468
    | exact resolve eq3468 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq3492 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3467 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3467
    | (have j0 := eq3467 X0
       grind)
    | exact resolve eq3467 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467
  have eq3503 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3491
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3491
    | exact resolve eq3491 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq3504 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3492 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3492
    | (have j0 := eq3492 X0
       grind)
    | exact resolve eq3492 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3492
  have eq6744 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq94 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq13929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq13929
    | exact resolve eq13929 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13929
  have eq13941 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq13930
       have r₂ := eq27
       grind)
    | exact resolve eq13930 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13930
  have eq13943 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq13941
    | exact resolve eq13941 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13941
  have eq14057 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq13943 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq13943
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq13943
       grind)
    | exact resolve eq13 eq13943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13943
  have eq14078 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq14057 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14057
  have eq14079 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq14078 X1
       grind)
    | exact superpose eq14078 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq14078 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq14078 X0
       grind)
    | exact resolve eq13 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14078
  have eq14100 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14079 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14079
  have eq14278 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq14100 (k sF2 sF2) x
       grind)
    | exact superpose eq14100 eq49
    | (have j1 := eq14100 X0 x
       grind)
    | exact resolve eq49 eq14100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14100
  have eq14358 : ∀ X0 : G, x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq14278
    | (have j0 := eq14278 x
       grind)
    | exact resolve eq14278 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14278
  have eq14386 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14358 X0
       have j1 := eq917 x X0
       grind)
    | (have r₁ := eq14358 X0
       have r₂ := eq917 x x
       grind)
    | (have r₁ := eq14358 x
       have r₂ := eq917 x x
       grind)
    | exact resolve eq14358 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14358
  have eq14425 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3504 x
       have i₂ := eq14386 x
       grind)
    | exact superpose eq14386 eq3504
    | (have j0 := eq3504 x
       grind)
    | (have r₁ := eq3504 x
       have r₂ := eq14386 x
       grind)
    | exact resolve eq3504 eq14386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14426 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq589 x
       have i₂ := eq14386 x
       grind)
    | exact superpose eq14386 eq589
    | (have j0 := eq589 x
       grind)
    | exact resolve eq589 eq14386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14386
  have eq14448 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14426
  have eq14449 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14425
  have eq14464 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14448
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14448
    | exact resolve eq14448 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448
  have eq14512 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x X0
       have i₂ := eq14449
       grind)
    | exact superpose eq14449 eq61
    | exact resolve eq61 eq14449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14449
  have eq14929 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq14464 eq61
    | exact resolve eq61 eq14464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14464
  have eq15891 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x X0
       have i₂ := eq14512 x
       grind)
    | exact superpose eq14512 eq61
    | exact resolve eq61 eq14512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14512
  have eq15984 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15891 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15891
    | (have j0 := eq15891 y
       grind)
    | exact resolve eq15891 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15891
  have eq16064 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15984 eq27
    | exact resolve eq27 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16066 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15984 eq75
    | (have r₁ := eq75
       have r₂ := eq15984
       grind)
    | exact resolve eq75 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15984
  have eq16077 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16066
  have eq16305 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f16305_14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = X1 := by
      intro X0 X1
      grind
    have f16305_15 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f16305_24 : X0 ≠ (M.op (σ x) X0) := by grind
    have f16305_25 : x ≠ (M.op x y) := by grind
    have f16305_26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f16305_27 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f16305_15 X0
         grind)
      | (have r₁ := f16305_15 X0
         have r₂ := f16305_25
         grind)
      | exact resolve f16305_15 f16305_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16305_28 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f16305_27 X0
         grind)
      | (have r₁ := f16305_27 X0
         have r₂ := f16305_26
         grind)
      | exact resolve f16305_27 f16305_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16305_31 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f16305_14 (σ x) X0
         have i₂ := f16305_28 (σ x)
         grind)
      | exact superpose f16305_28 f16305_14
      | exact resolve f16305_14 f16305_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16305_34 : X0 ≠ X0 := by
      first
      | (have i₁ := f16305_24
         have i₂ := f16305_31 X0
         grind)
      | exact superpose f16305_31 f16305_24
      | (have r₁ := f16305_24
         have r₂ := f16305_31 X0
         grind)
      | exact resolve f16305_24 f16305_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16305_39 : False := by grind
    exact f16305_39
  clear eq14929
  have eq16399 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16305
    | (have j0 := eq16305 (σ y)
       grind)
    | exact resolve eq16305 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16305
  have eq16480 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16399 eq27
    | exact resolve eq27 eq16399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16399
  have eq112188 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16077 eq112
    | exact resolve eq112 eq16077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16077
  have eq112260 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq112188
  have eq112274 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq112260
       have r₂ := eq16064
       grind)
    | exact resolve eq112260 eq16064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16064 eq112260
  have eq144925 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq112274 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq112274
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq112274
       grind)
    | exact resolve eq13 eq112274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112274
  have eq144949 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq144925 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144925
  have eq182346 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq144949 X1
       grind)
    | exact superpose eq144949 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq144949 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq144949 X0
       grind)
    | exact resolve eq13 eq144949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144949
  have eq182370 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq182346 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182346
  have eq188514 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq182370 (k sF2 sF2) x
       grind)
    | exact superpose eq182370 eq49
    | (have j1 := eq182370 X0 x
       grind)
    | exact resolve eq49 eq182370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq182370
  have eq188972 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq188514
    | (have j0 := eq188514 x
       grind)
    | exact resolve eq188514 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188514
  have eq189086 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq188972 X0
       have j1 := eq917 x X0
       grind)
    | (have r₁ := eq188972 X0
       have r₂ := eq917 x x
       grind)
    | (have r₁ := eq188972 x
       have r₂ := eq917 x x
       grind)
    | exact resolve eq188972 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188972
  have eq189366 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3504 x
       have i₂ := eq189086 x
       grind)
    | exact superpose eq189086 eq3504
    | (have j0 := eq3504 x
       grind)
    | (have r₁ := eq3504 x
       have r₂ := eq189086 x
       grind)
    | exact resolve eq3504 eq189086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189086
  have eq189471 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq189366
  have eq190038 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0
       have i₂ := eq189471
       grind)
    | exact superpose eq189471 eq61
    | exact resolve eq61 eq189471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189471
  have eq203558 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0
       have i₂ := eq190038 x
       grind)
    | exact superpose eq190038 eq61
    | exact resolve eq61 eq190038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190038
  have eq203769 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq203558 y
       grind)
    | exact superpose eq203558 eq18
    | (have j1 := eq203558 y
       grind)
    | exact resolve eq18 eq203558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203558
  have eq203877 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq203769
  have eq203943 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203877 eq20
    | exact resolve eq20 eq203877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203997 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq203877 eq293
    | exact resolve eq293 eq203877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq204173 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq204259 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq203997 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq203997
    | exact resolve eq203997 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq203997
  have eq204306 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq203943
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq203943
    | exact resolve eq203943 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203943
  have eq204903 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq204306 eq26
    | exact resolve eq26 eq204306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205020 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq204306 eq16480
    | (have r₁ := eq16480
       have r₂ := eq204306
       grind)
    | exact resolve eq16480 eq204306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16480 eq204306
  have eq205163 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq205020
  have eq205164 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq205163
  have eq205260 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205164 eq75
    | (have r₁ := eq75
       have r₂ := eq205164
       grind)
    | exact resolve eq75 eq205164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq205164
  have eq205273 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq205260
  have eq216942 : (τ (σ (M.op x y))) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq112 eq204259
    | exact resolve eq204259 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq204259
  have eq217396 : (τ (σ (M.op x y))) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq216942
  have eq217711 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq140 eq217396
    | exact resolve eq217396 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq217396
  have eq217760 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq217711
    | exact resolve eq217711 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq217711
  have eq217800 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq217760
       have r₂ := eq13 x x
       grind)
    | exact resolve eq217760 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217760
  have eq217853 : y = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq203877 eq217800
    | exact resolve eq217800 eq203877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203877 eq217800
  have eq217915 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq217853
       have r₂ := eq204173
       grind)
    | exact resolve eq217853 eq204173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204173 eq217853
  have eq219076 : (σ (k y x)) = (k (k (σ y) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq160
       have i₂ := eq217915
       grind)
    | exact superpose eq217915 eq160
    | exact resolve eq160 eq217915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq217915
  have eq219126 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq219076
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq219076
    | exact resolve eq219076 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq219076
  have eq331356 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205273 eq219126
    | exact resolve eq219126 eq205273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205273 eq219126
  have eq331453 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq331356
  have eq331495 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq331453
       have r₂ := eq3503
       grind)
    | exact resolve eq331453 eq3503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3503 eq331453
  have eq331559 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq331495 eq61
    | exact resolve eq61 eq331495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331495
  have eq350588 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f350588_13 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = X1 := by
      intro X0 X1
      grind
    have f350588_14 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
      intro X0
      grind
    have f350588_23 : X0 ≠ (M.op (σ x) X0) := by grind
    have f350588_24 : x ≠ (M.op x y) := by grind
    have f350588_25 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f350588_14 X0
         grind)
      | (have r₁ := f350588_14 X0
         have r₂ := f350588_24
         grind)
      | exact resolve f350588_14 f350588_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f350588_28 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f350588_13 (σ x) X0
         have i₂ := f350588_25 (σ x)
         grind)
      | exact superpose f350588_25 f350588_13
      | exact resolve f350588_13 f350588_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f350588_31 : X0 ≠ X0 := by
      first
      | (have i₁ := f350588_23
         have i₂ := f350588_28 X0
         grind)
      | exact superpose f350588_28 f350588_23
      | (have r₁ := f350588_23
         have r₂ := f350588_28 X0
         grind)
      | exact resolve f350588_23 f350588_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f350588_34 : False := by grind
    exact f350588_34
  clear eq331559
  have eq350798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq350588 eq204903
    | exact resolve eq204903 eq350588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204903 eq350588
  have eq350999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq350798
  have eq351030 : x = (M.op x y) := by
    first
    | (have r₁ := eq350999
       have r₂ := eq27
       grind)
    | exact resolve eq350999 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350999
  have eq352025 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq351030 eq20
    | exact resolve eq20 eq351030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq352031 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq351030 eq74
    | (have r₁ := eq74
       have r₂ := eq351030
       grind)
    | exact resolve eq74 eq351030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq352202 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq352031
  have eq352348 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq352025
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq352025
    | exact resolve eq352025 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352025
  have eq352351 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq352348 eq26
    | exact resolve eq26 eq352348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361761 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6744 x
       have i₂ := eq352202
       grind)
    | exact superpose eq352202 eq6744
    | (have j0 := eq6744 x
       grind)
    | exact resolve eq6744 eq352202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6744 eq352202
  have eq361773 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq361761
  have eq361784 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq361773
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq361773
    | exact resolve eq361773 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361773
  have eq361811 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq361784
    | exact resolve eq361784 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq361784
  have eq361836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq352348 eq361811
    | exact resolve eq361811 eq352348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361811
  have eq361858 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq361836
       have r₂ := eq27
       grind)
    | exact resolve eq361836 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361836
  have eq361868 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq361858
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq361858
    | exact resolve eq361858 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361858
  have eq361877 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq352348 eq361868
    | exact resolve eq361868 eq352348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361868
  have eq362290 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq361877 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq361877
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq361877
       grind)
    | exact resolve eq13 eq361877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361877
  have eq362318 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq362290 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362290
  have eq362682 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq362318 X1
       grind)
    | exact superpose eq362318 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq362318 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq362318 X0
       grind)
    | exact resolve eq13 eq362318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362318
  have eq362710 : ∀ X0 X1 : G, (k X1 (σ (M.op x y))) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq362682 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362682
  have eq362806 : ∀ X0 : G, (τ (σ x)) = (k x (M.op x y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq57
       have i₂ := eq362710 (k sF2 sF1) x
       grind)
    | exact superpose eq362710 eq57
    | (have j1 := eq362710 X0 x
       grind)
    | exact resolve eq57 eq362710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq362710
  have eq363233 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq351030 eq362806
    | (have j0 := eq362806 X0
       grind)
    | exact resolve eq362806 eq351030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362806
  have eq363432 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq363233
    | (have j0 := eq363233 x
       grind)
    | exact resolve eq363233 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq363233
  have eq363536 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq363432 X0
       have j1 := eq917 x X0
       grind)
    | (have r₁ := eq363432 X0
       have r₂ := eq917 x x
       grind)
    | (have r₁ := eq363432 x
       have r₂ := eq917 x x
       grind)
    | exact resolve eq363432 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq363432
  have eq363971 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq589 x
       have i₂ := eq363536 x
       grind)
    | exact superpose eq363536 eq589
    | (have j0 := eq589 x
       grind)
    | exact resolve eq589 eq363536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq363978 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3504 x
       have i₂ := eq363536 x
       grind)
    | exact superpose eq363536 eq3504
    | (have j0 := eq3504 x
       grind)
    | (have r₁ := eq3504 x
       have r₂ := eq363536 x
       grind)
    | exact resolve eq3504 eq363536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504 eq363536
  have eq364173 : x = (M.op x x) := by grind
  clear eq363978
  have eq364178 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq363971
  have eq364348 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq364178
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq364178
    | exact resolve eq364178 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364178
  have eq364603 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq352348 eq364348
    | exact resolve eq364348 eq352348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364348
  have eq365157 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 x X0
       have i₂ := eq364173
       grind)
    | exact superpose eq364173 eq61
    | exact resolve eq61 eq364173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq365200 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq365157 X0
       have i₂ := eq364173
       grind)
    | exact superpose eq364173 eq365157
    | exact resolve eq365157 eq364173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364173 eq365157
  have eq366366 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq365200 y
       grind)
    | exact superpose eq365200 eq18
    | (have j1 := eq365200 y
       grind)
    | exact resolve eq18 eq365200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq365200
  have eq366518 : x = y := by
    first
    | exact superpose eq351030 eq366366
    | exact resolve eq366366 eq351030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351030 eq366366
  have eq366529 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq366518
       grind)
    | exact superpose eq366518 eq24
    | exact resolve eq24 eq366518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq366518
  have eq367031 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq366529
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq366529
    | exact resolve eq366529 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq366529
  have eq367195 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq352348 eq367031
    | exact resolve eq367031 eq352348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352348 eq367031
  have eq370255 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq367195 eq352351
    | exact resolve eq352351 eq367195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352351 eq367195
  have eq370269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq364603 eq370255
    | exact resolve eq370255 eq364603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364603 eq370255
  have eq370346 : False := by grind
  exact eq370346

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxx_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq53 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq50
    | exact resolve eq50 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq80 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq79
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq79
    | exact resolve eq79 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq77
    | exact resolve eq77 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq77
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq420 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq53
    | exact resolve eq53 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq420 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq53 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq53 eq420
    | exact resolve eq420 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq1098 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1028 X0 X1
       have i₂ := eq82 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq82 eq1028
    | exact resolve eq1028 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1028
  have eq1110 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1098 X0 X1
       have i₂ := eq53 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq1098 X0 X1
       have i₂ := eq53 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq53 eq1098
    | exact resolve eq1098 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq24919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq24920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq24919
    | exact resolve eq24919 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24919
  have eq24931 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24920
       have r₂ := eq28
       grind)
    | exact resolve eq24920 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24920
  have eq24935 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq24931 eq80
    | exact resolve eq80 eq24931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24931
  have eq25007 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq24935
    | exact resolve eq24935 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24935
  have eq25008 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25007
  have eq25022 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq25008
       grind)
    | exact superpose eq25008 eq53
    | exact resolve eq53 eq25008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25008
  have eq25294 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq25022 x
       grind)
    | exact superpose eq25022 eq53
    | exact resolve eq53 eq25022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq25302 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1110 x X0
       have i₂ := eq25022 x
       grind)
    | exact superpose eq25022 eq1110
    | exact resolve eq1110 eq25022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq25022
  have eq25446 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25302 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25302
    | (have j0 := eq25302 X0
       grind)
    | exact resolve eq25302 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25302
  have eq25451 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq25294 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25294
    | (have j0 := eq25294 y
       grind)
    | exact resolve eq25294 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25294
  have eq25615 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25451 eq30
    | exact resolve eq30 eq25451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25451
  have eq25733 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq25615
    | exact resolve eq25615 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25615
  have eq25734 : y = (M.op x y) ∨ x = y := by grind
  clear eq25733
  have eq25895 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq25734 eq21
    | exact resolve eq21 eq25734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25734
  have eq26008 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25895
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25895
    | exact resolve eq25895 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25895
  have eq26024 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq26008 eq27
    | exact resolve eq27 eq26008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26008
  have eq28253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq25446 eq26024
    | exact resolve eq26024 eq25446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25446 eq26024
  have eq28363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq28253
  have eq28409 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq28363
       have r₂ := eq28
       grind)
    | exact resolve eq28363 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28363
  have eq28418 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq28409 eq30
    | exact resolve eq30 eq28409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28409
  have eq28565 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq28418
    | exact resolve eq28418 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28418
  have eq28566 : x = y := by grind
  clear eq28565
  have eq28582 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq28566
       grind)
    | exact superpose eq28566 eq19
    | exact resolve eq19 eq28566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28583 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28566
       grind)
    | exact superpose eq28566 eq25
    | exact resolve eq25 eq28566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28566
  have eq28696 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28583
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28583
    | exact resolve eq28583 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq28583
  have eq28712 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28696 eq27
    | exact resolve eq27 eq28696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28696
  have eq28976 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq28712 eq80
    | exact resolve eq80 eq28712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq28712
  have eq29044 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq28976
       have i₂ := eq28582
       grind)
    | exact superpose eq28582 eq28976
    | exact resolve eq28976 eq28582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28582 eq28976
  have eq29051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29044 eq15
    | exact resolve eq15 eq29044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29044
  have eq29100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq29051
    | exact resolve eq29051 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq29051
  have eq29109 : False := by grind
  exact eq29109

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq20 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq20 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq83 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
  have eq136 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq53 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq53 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq139 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq136 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq303 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq16
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq391 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq139 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq34 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq34 eq139
    | (have j0 := eq139 (M.op (M.op X0 X0) X0) X1
       grind)
    | exact resolve eq139 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq402 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq20 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq391 X0 X1
       have i₂ := eq20 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq20 eq391
    | (have j0 := eq391 X0 X1
       grind)
    | exact resolve eq391 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq391
  have eq403 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq402 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq652 : ∀ X0 X1 : G, (σ (k X0 (M.op (M.op X1 X1) X1))) = (M.op (σ X0) (σ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq403 X1 (σ X0)
       grind)
    | exact superpose eq403 eq15
    | exact resolve eq15 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq672 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op (M.op X1 X1) X1))) = (σ (M.op X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq652
    | exact resolve eq652 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq652
  have eq709 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq743 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq709 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq709
    | (have j0 := eq709 X0 X1
       grind)
    | exact resolve eq709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq1407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq303
       have i₂ := eq743 x y
       grind)
    | exact superpose eq743 eq303
    | (have j1 := eq743 (σ x) (σ y)
       grind)
    | (have r₁ := eq303
       have r₂ := eq743 x y
       grind)
    | (have r₁ := eq303
       have r₂ := eq743 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq303
       have r₂ := eq743 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq303 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq743
  have eq1408 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq1407
  have eq1453 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq83 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq83 X0
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1466 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1453 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453
  have eq41238 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1466 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1466
    | exact resolve eq1466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq41463 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41238 X0 X1
       have i₂ := eq31 (σ X0) X0
       grind)
    | exact superpose eq31 eq41238
    | (have j0 := eq41238 X0 X1
       grind)
    | exact resolve eq41238 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq41238
  have eq41477 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41463 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41463
    | (have j0 := eq41463 X0 X0
       grind)
    | exact resolve eq41463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41463
  have eq41614 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41477 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41477
  have eq41615 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41614
  have eq42445 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq41615 (σ X0)
       grind)
    | exact superpose eq41615 eq15
    | exact resolve eq15 eq41615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42516 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq42445 X0
       have i₂ := eq41615 X0
       grind)
    | exact superpose eq41615 eq42445
    | exact resolve eq42445 eq41615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41615 eq42445
  have eq1061877 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq16
    | exact resolve eq16 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1061924 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1061877
       have r₂ := eq42516 x
       grind)
    | exact resolve eq1061877 eq42516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061877
  have eq1061925 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1061924
       have i₂ := eq42516 y
       grind)
    | exact superpose eq42516 eq1061924
    | exact resolve eq1061924 eq42516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061924
  have eq1061927 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1061925
       grind)
    | exact superpose eq1061925 eq10
    | exact resolve eq10 eq1061925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061925
  have eq1062379 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1061927
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1061927
    | exact resolve eq1061927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061927
  have eq1062473 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1062379
       grind)
    | exact superpose eq1062379 eq16
    | exact resolve eq16 eq1062379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062379
  have eq1062520 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1062473
       have r₂ := eq42516 x
       grind)
    | exact resolve eq1062473 eq42516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42516 eq1062473
  have eq1064694 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1062520
       grind)
    | exact superpose eq1062520 eq10
    | exact resolve eq10 eq1062520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062520
  have eq1065143 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1064694
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1064694
    | exact resolve eq1064694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064694
  have eq1065144 : y = (M.op y y) := by grind
  clear eq1065143
  have eq1065297 : ∀ X0 : G, (M.op (σ X0) (σ (M.op y y))) = (σ (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq672 X0 y
       have i₂ := eq1065144
       grind)
    | exact superpose eq1065144 eq672
    | exact resolve eq672 eq1065144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq1065874 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1065297 X0
       have i₂ := eq1065144
       grind)
    | exact superpose eq1065144 eq1065297
    | exact resolve eq1065297 eq1065144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065144 eq1065297
  have eq1133574 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1065874 x
       grind)
    | exact superpose eq1065874 eq16
    | (have r₁ := eq16
       have r₂ := eq1065874 x
       grind)
    | exact resolve eq16 eq1065874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065874
  have eq1134110 : False := by grind
  exact eq1134110
