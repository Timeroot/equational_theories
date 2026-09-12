import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pyy_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq44
    | (have j1 := eq72 x x
       grind)
    | exact resolve eq44 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq373 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq377 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq375 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq375
    | exact resolve eq375 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq679 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq105 eq72
    | (have j0 := eq72 (σ x) x
       grind)
    | exact resolve eq72 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq680 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq679
    | exact resolve eq679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq683 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq680
       have r₂ := eq27
       grind)
    | exact resolve eq680 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq690 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq683 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq683
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq683
       grind)
    | exact resolve eq13 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq690 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq710 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq691 eq49
    | exact resolve eq49 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq691
  have eq890 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq683 eq710
    | exact resolve eq710 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq710
  have eq903 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq890
  have eq905 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq903
    | exact resolve eq903 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq903
  have eq910 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72 x x
       have i₂ := eq905
       grind)
    | exact superpose eq905 eq72
    | (have j0 := eq72 x x
       grind)
    | exact resolve eq72 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq911 : x = (M.op x x) := by grind
  clear eq910
  have eq953 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq911
       grind)
    | exact superpose eq911 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq911
       grind)
    | exact resolve eq13 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq911
       grind)
    | exact superpose eq911 eq14
    | exact resolve eq14 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq960 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq957 X0
       have i₂ := eq377 x X0
       grind)
    | (have i₁ := eq957 X0
       have i₂ := eq377 x (M.op x X0)
       grind)
    | exact superpose eq377 eq957
    | exact resolve eq957 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq957
  have eq968 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq958 x
       grind)
    | exact superpose eq958 eq43
    | exact resolve eq43 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq958
  have eq976 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq968
       have i₂ := eq911
       grind)
    | exact superpose eq911 eq968
    | exact resolve eq968 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq977 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq976
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq976
    | exact resolve eq976 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq976
  have eq982 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq977 eq72
    | (have j0 := eq72 (σ x) x
       grind)
    | exact resolve eq72 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq977
  have eq983 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq982
  have eq1003 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq960 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq960
    | (have j0 := eq960 y
       grind)
    | exact resolve eq960 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1011 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq960 X0
       grind)
    | exact superpose eq960 eq14
    | exact resolve eq14 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1017 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1011 X0
       have i₂ := eq911
       grind)
    | exact superpose eq911 eq1011
    | exact resolve eq1011 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1024 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq1003 eq50
    | exact resolve eq50 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1003
  have eq1030 : y = (M.op x y) := by
    first
    | (have i₁ := eq1024
       have i₂ := eq911
       grind)
    | exact superpose eq911 eq1024
    | exact resolve eq1024 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq1024
  have eq1033 : y = (M.op x y) := by
    first
    | (have i₁ := eq1030
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1030
    | exact resolve eq1030 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1030
  have eq1034 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1033 eq20
    | exact resolve eq20 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1033
  have eq1060 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1034
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1034
    | exact resolve eq1034 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1034
  have eq1062 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1060 eq26
    | exact resolve eq26 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1087 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq960 X0
       have i₂ := eq1017 X0
       grind)
    | exact superpose eq1017 eq960
    | exact resolve eq960 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1191 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 x) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq373 X0 x
       have i₂ := eq1087 (M.op X0 sF2)
       grind)
    | exact superpose eq1087 eq373
    | exact resolve eq373 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq1220 : (σ x) = (M.op (M.op x (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1191 x
       have i₂ := eq1087 x
       grind)
    | exact superpose eq1087 eq1191
    | exact resolve eq1191 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087 eq1191
  have eq1228 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1220
       have i₂ := eq1017 sF4
       grind)
    | exact superpose eq1017 eq1220
    | exact resolve eq1220 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq1220
  have eq1233 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1228 eq51
    | exact resolve eq51 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1228
  have eq1239 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1060 eq1233
    | exact resolve eq1233 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060 eq1233
  have eq1242 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq983 eq1239
    | exact resolve eq1239 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983 eq1239
  have eq1250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1062 eq1242
    | exact resolve eq1242 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq1242
  have eq1251 : False := by grind
  exact eq1251

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_x_pyx_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq59 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq112 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X1 (M.op (M.op X1 X0) X2))) = (k (M.op X1 (M.op (M.op X1 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X0) X2))) = (k (M.op X1 (M.op (M.op X1 X0) X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq112 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq333 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq38
  have eq347 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) (M.op X0 X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq61 X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X4 X5
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq59 eq61
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
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
  have eq356 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq361 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq361
    | exact resolve eq361 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq367 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq353
    | (have j0 := eq353 X0 X1
       grind)
    | exact resolve eq353 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq368 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq352 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq352
    | exact resolve eq352 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq388 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq365 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq365
    | (have j0 := eq365 x y
       grind)
    | exact resolve eq365 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq365
    | (have j0 := eq365 (σ x) (σ y)
       grind)
    | exact resolve eq365 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) = (k (M.op X0 (M.op (M.op X0 X1) X2)) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113 (M.op X0 x) X0 X2
       have i₂ := eq365 X0 x
       grind)
    | exact superpose eq365 eq113
    | (have j0 := eq113 (M.op X0 X1) X1 X2
       grind)
    | exact resolve eq113 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op (M.op X2 X0) X3)) X0)) = (k (M.op (M.op X2 (M.op (M.op X2 X0) X3)) X0) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq113
    | (have j0 := eq113 (M.op X0 X1) X1 X2
       grind)
    | exact resolve eq113 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq568
    | (have j0 := eq568 X0 X1 x x
       grind)
    | exact resolve eq568 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq713 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq714 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq713 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq3142 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq367 eq61
    | exact resolve eq61 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3157 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3142 eq367
    | exact resolve eq367 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq3142
  have eq3174 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368 X1 (M.op (M.op X1 X0) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq368
    | exact resolve eq368 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3182 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq60 eq368
    | exact resolve eq368 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq3213 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq368 X0 X0 x
       grind)
    | exact superpose eq368 eq61
    | exact resolve eq61 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3235 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq3182
    | (have j0 := eq3182 X0
       grind)
    | exact resolve eq3182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3182
  have eq3244 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq355 x x
       have i₂ := eq3213 x
       grind)
    | exact superpose eq3213 eq355
    | exact resolve eq355 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3245 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq356 sF2 sF2
       have i₂ := eq3213 sF2
       grind)
    | exact superpose eq3213 eq356
    | exact resolve eq356 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq3246 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq368 X0 X0 X0
       have i₂ := eq3213 X0
       grind)
    | exact superpose eq3213 eq368
    | exact resolve eq368 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3305 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq714 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq714
    | (have j0 := eq714 (τ X0)
       grind)
    | exact resolve eq714 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq714
  have eq3313 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3305 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3305
    | (have j0 := eq3305 X0
       grind)
    | exact resolve eq3305 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3305
  have eq3319 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3313 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3313
    | (have j0 := eq3313 X0
       grind)
    | exact resolve eq3313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313
  have eq3416 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) (M.op X0 X5)) (M.op X0 X6)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq347 X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X4 X5 X6
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq347
    | exact resolve eq347 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5042 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3246 X0
       grind)
    | exact superpose eq3246 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3246 X0
       grind)
    | exact resolve eq13 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5052 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5042 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042
  have eq5087 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq333 X0 (M.op X1 X1)
       have i₂ := eq5052 X1 (σ X0)
       grind)
    | exact superpose eq5052 eq333
    | exact resolve eq333 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq5052
  have eq5107 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5087 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq5087
    | exact resolve eq5087 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5087
  have eq6036 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) (M.op X0 X5)) (M.op X0 X6)) (M.op X0 X7)) (M.op X0 X8)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq348 X0 (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X5 X6 X7 X8
       have i₂ := eq347 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq347 eq348
    | exact resolve eq348 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq348
  have eq17241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq17241
    | exact resolve eq17241 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17241
  have eq17259 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq17248
       have r₂ := eq27
       grind)
    | exact resolve eq17248 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17248
  have eq17261 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq17259
    | exact resolve eq17259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17259
  have eq17273 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17261 eq5107
    | exact resolve eq5107 eq17261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107 eq17261
  have eq17315 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq17273
    | exact resolve eq17273 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17273
  have eq17324 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17315 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq17315 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq17315 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17315
  have eq17370 : y ≠ y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3319 y
       have i₂ := eq17324 y
       grind)
    | exact superpose eq17324 eq3319
    | (have j0 := eq3319 y
       grind)
    | (have r₁ := eq3319 y
       have r₂ := eq17324 y
       grind)
    | exact resolve eq3319 eq17324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17324
  have eq17399 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17370
  have eq17508 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq368 y y x
       have i₂ := eq17399
       grind)
    | exact superpose eq17399 eq368
    | exact resolve eq368 eq17399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17512 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17508 X0
       have i₂ := eq365 y X0
       grind)
    | (have i₁ := eq17508 X0
       have i₂ := eq365 y (M.op y X0)
       grind)
    | exact superpose eq365 eq17508
    | exact resolve eq17508 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17508
  have eq20266 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq17512 X0
       grind)
    | exact superpose eq17512 eq14
    | exact resolve eq14 eq17512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21434 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20266 X0
       have i₂ := eq17399
       grind)
    | exact superpose eq17399 eq20266
    | exact resolve eq20266 eq17399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17399 eq20266
  have eq21512 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21434 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21434
  have eq21516 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17512 X0
       have i₂ := eq21512 X0
       grind)
    | exact superpose eq21512 eq17512
    | exact resolve eq17512 eq21512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17512 eq21512
  have eq21589 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21516 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21516
  have eq21660 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21589 x
       grind)
    | exact superpose eq21589 eq18
    | (have j1 := eq21589 x
       grind)
    | exact resolve eq18 eq21589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21589
  have eq21696 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21660
  have eq21724 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21696 eq3245
    | exact resolve eq3245 eq21696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245
  have eq21802 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21724 eq368
    | exact resolve eq368 eq21724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21806 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (σ x) X0)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21724 eq14
    | exact resolve eq14 eq21724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21831 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21802
       have i₂ := eq3213 sF2
       grind)
    | exact superpose eq3213 eq21802
    | exact resolve eq21802 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21802
  have eq24936 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21696 eq3235
    | exact resolve eq3235 eq21696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235
  have eq29650 : (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq21806
    | (have j0 := eq21806 (σ y)
       grind)
    | exact resolve eq21806 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29696 : (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21696 eq29650
    | exact resolve eq29650 eq21696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21696 eq29650
  have eq29735 : (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq29696
  have eq30666 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21831 eq368
    | exact resolve eq368 eq21831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21831
  have eq31178 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30666 eq14
    | exact resolve eq14 eq30666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31179 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ y) X0)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30666 eq61
    | exact resolve eq61 eq30666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq30666
  have eq31222 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ y) X0)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq31179 X0
       have i₂ := eq3246 sF2
       grind)
    | exact superpose eq3246 eq31179
    | exact resolve eq31179 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31179
  have eq31223 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31178
       have i₂ := eq3246 sF2
       grind)
    | exact superpose eq3246 eq31178
    | exact resolve eq31178 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31178
  have eq31224 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31223 eq21724
    | exact resolve eq21724 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21724
  have eq31225 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31223 eq21806
    | exact resolve eq21806 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21806
  have eq31229 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31223 eq29735
    | exact resolve eq29735 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29735 eq31223
  have eq31272 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq31229
  have eq31276 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31225
  have eq31277 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq31224
  have eq31878 : (k (M.op (σ y) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31272 eq113
    | (have j0 := eq113 (σ y) x x
       grind)
    | exact resolve eq113 eq31272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq31272
  have eq31921 : (M.op (σ y) (σ x)) = (k (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31878
       have i₂ := eq365 sF3 (M.op sF3 sF2)
       grind)
    | (have i₁ := eq31878
       have i₂ := eq365 sF3 sF2
       grind)
    | exact superpose eq365 eq31878
    | exact resolve eq31878 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31878
  have eq31923 : (M.op (σ y) (σ x)) = (k (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op (σ y) (σ x)) (σ y)
       grind)
    | (have r₁ := eq31921
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq31921 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31921
  have eq32467 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24936 eq31276
    | exact resolve eq31276 eq24936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24936 eq31276
  have eq32512 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq32467 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32467
  have eq32971 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31277 eq31923
    | exact resolve eq31923 eq31277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31277 eq31923
  have eq32980 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq32971
  have eq33045 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32980 eq90
    | exact resolve eq90 eq32980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq32980
  have eq33063 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq33045
  have eq33183 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq368 y y x
       have i₂ := eq33063
       grind)
    | exact superpose eq33063 eq368
    | exact resolve eq368 eq33063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33192 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq33183 X0
       have i₂ := eq365 y X0
       grind)
    | (have i₁ := eq33183 X0
       have i₂ := eq365 y (M.op y X0)
       grind)
    | exact superpose eq365 eq33183
    | exact resolve eq33183 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33183
  have eq36495 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32512 eq14
    | exact resolve eq14 eq32512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32512
  have eq62139 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq33192 X0
       grind)
    | exact superpose eq33192 eq14
    | exact resolve eq14 eq33192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68942 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq62139 X0
       have i₂ := eq33063
       grind)
    | exact superpose eq33063 eq62139
    | exact resolve eq62139 eq33063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33063 eq62139
  have eq69042 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq68942 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68942
  have eq69406 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq33192 X0
       have i₂ := eq69042 X0
       grind)
    | exact superpose eq69042 eq33192
    | exact resolve eq33192 eq69042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33192 eq69042
  have eq69494 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq69406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69406
  have eq69581 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq69494 x
       grind)
    | exact superpose eq69494 eq18
    | (have j1 := eq69494 x
       grind)
    | exact resolve eq18 eq69494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69494
  have eq69683 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq69581
  have eq69702 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69683 eq28
    | exact resolve eq28 eq69683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq69703 : ∀ X0 : G, (σ (k x X0)) = (k (σ (M.op x y)) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq69683 eq35
    | exact resolve eq35 eq69683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq69683
  have eq70013 : ∀ X0 : G, (σ (k x X0)) = (σ (k (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq69703
    | exact resolve eq69703 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq69703
  have eq70014 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq69702
    | exact resolve eq69702 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq69702
  have eq90055 : ∀ X0 : G, (k (M.op x y) X0) = (τ (σ (k x X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq70013 eq16
    | exact resolve eq16 eq70013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70013
  have eq90226 : ∀ X0 : G, (k x X0) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90055 X0
       have i₂ := eq16 (k x X0)
       grind)
    | exact superpose eq16 eq90055
    | exact resolve eq90055 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90055
  have eq364445 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36495 eq31222
    | exact resolve eq31222 eq36495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31222 eq36495
  have eq364548 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq364445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364445
  have eq364620 : x = (M.op (M.op (M.op (σ y) (σ y)) (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq364548 eq355
    | exact resolve eq355 eq364548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq364662 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq364548 eq14
    | exact resolve eq14 eq364548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364548
  have eq386290 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq364662 eq364620
    | exact resolve eq364620 eq364662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364620 eq364662
  have eq386387 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq386290
  have eq386398 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq386387 eq59
    | exact resolve eq59 eq386387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq386479 : (M.op x (M.op x y)) = (k (M.op x y) x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq386387 eq584
    | exact resolve eq584 eq386387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq386387
  have eq386525 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq388 eq386479
    | exact resolve eq386479 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq386479
  have eq386540 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq386525
       have r₂ := eq13 x x
       grind)
    | exact resolve eq386525 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386525
  have eq386603 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq386540 eq90226
    | exact resolve eq90226 eq386540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90226 eq386540
  have eq386617 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq386603
  have eq393382 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3319 x
       have i₂ := eq386617
       grind)
    | exact superpose eq386617 eq3319
    | (have j0 := eq3319 x
       grind)
    | exact resolve eq3319 eq386617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319 eq386617
  have eq393423 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq393382
       have r₂ := eq70014
       grind)
    | exact resolve eq393382 eq70014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70014 eq393382
  have eq435225 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X2)) = (k (M.op X0 (M.op (M.op X0 X1) X2)) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq554 X0 X1 X2
       have i₂ := eq3174 X1 X0 X2
       grind)
    | exact superpose eq3174 eq554
    | (have j0 := eq554 X0 X1 X2
       grind)
    | exact resolve eq554 eq3174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq3174
  have eq435226 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X2)) = (k (M.op X0 (M.op (M.op X0 X1) X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq435225 X0 X1 X2
       have j1 := eq13 (M.op X0 (M.op (M.op X0 X1) X2)) (M.op X0 X1)
       grind)
    | (have r₁ := eq435225 X0 X1 X2
       have r₂ := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq435225 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435225
  have eq436419 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq386398
       have i₂ := eq393423
       grind)
    | exact superpose eq393423 eq386398
    | exact resolve eq386398 eq393423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386398 eq393423
  have eq436534 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq436419
  have eq436570 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq436534
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq436534
    | exact resolve eq436534 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq436534
  have eq436571 : y = (M.op x y) := by grind
  clear eq436570
  have eq436573 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq436571 eq20
    | exact resolve eq20 eq436571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq436759 : x = (M.op (M.op (M.op x x) y) x) := by
    first
    | exact superpose eq436571 eq3244
    | exact resolve eq3244 eq436571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3244
  have eq437010 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq436573
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq436573
    | exact resolve eq436573 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq436573
  have eq437019 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq437010 eq26
    | exact resolve eq26 eq437010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq440143 : (M.op (M.op x x) x) = (k (M.op (M.op x x) x) (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq435226 (M.op x x) y x
       have i₂ := eq436759
       grind)
    | exact superpose eq436759 eq435226
    | exact resolve eq435226 eq436759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435226 eq436759
  have eq440244 : x = (k x (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq440143
       have i₂ := eq3213 x
       grind)
    | exact superpose eq3213 eq440143
    | exact resolve eq440143 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213 eq440143
  have eq480776 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) X1)) (M.op (M.op (M.op x y) (M.op x y)) X2)) (M.op (M.op (M.op x y) (M.op x y)) X3)) (M.op (M.op (M.op x y) (M.op x y)) X4)) (M.op (M.op (M.op x y) (M.op x y)) X5)) (M.op (M.op x y) (M.op x y))) (M.op (M.op (M.op x y) (M.op x y)) X6)) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | exact superpose eq3157 eq6036
    | exact resolve eq6036 eq3157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157 eq6036
  have eq482064 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op y y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op y y)) X1)) (M.op (M.op y y) X2)) (M.op (M.op y y) X3)) (M.op (M.op y y) X4)) (M.op (M.op y y) X5)) (M.op y y)) (M.op (M.op y y) X6)) (M.op y y)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | exact superpose eq436571 eq480776
    | exact resolve eq480776 eq436571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436571 eq480776
  have eq483107 : ∀ X6 : G, (M.op y y) = (M.op (M.op (M.op y y) (M.op (M.op y y) X6)) (M.op y y)) := by
    intro X6
    first
    | (have i₁ := eq482064 x x x x x x X6
       have i₂ := eq3416 (M.op y y) x x x x x x
       grind)
    | exact superpose eq3416 eq482064
    | exact resolve eq482064 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416 eq482064
  have eq483539 : ∀ X6 : G, (M.op y y) = (M.op (M.op (M.op y y) X6) (M.op y y)) := by
    intro X6
    first
    | (have i₁ := eq483107 X6
       have i₂ := eq365 (M.op y y) X6
       grind)
    | (have i₁ := eq483107 X6
       have i₂ := eq365 (M.op y y) (M.op (M.op y y) X6)
       grind)
    | exact superpose eq365 eq483107
    | exact resolve eq483107 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq483107
  have eq599713 : ∀ X0 : G, (M.op (M.op (M.op y y) (M.op y y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op y y) (M.op y y)
       have i₂ := eq483539 X0
       grind)
    | exact superpose eq483539 eq14
    | exact resolve eq14 eq483539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483539
  have eq599951 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq599713 X0
       have i₂ := eq3246 y
       grind)
    | exact superpose eq3246 eq599713
    | exact resolve eq599713 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246 eq599713
  have eq609167 : ∀ X0 X1 : G, (M.op (M.op y y) X0) = (M.op (M.op (M.op (M.op y y) X0) X1) (M.op (M.op y y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq368 (M.op y y) X0 X1
       have i₂ := eq599951 (M.op (M.op (M.op y y) X0) X1)
       grind)
    | exact superpose eq599951 eq368
    | exact resolve eq368 eq599951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq609503 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq609167 X0 X1
       have i₂ := eq599951 X0
       grind)
    | exact superpose eq599951 eq609167
    | exact resolve eq609167 eq599951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599951 eq609167
  have eq611767 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq609503 X0 X1
       grind)
    | exact superpose eq609503 eq14
    | exact resolve eq14 eq609503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617753 : x = (k x y) := by
    first
    | (have i₁ := eq440244
       have i₂ := eq611767 x y
       grind)
    | exact superpose eq611767 eq440244
    | exact resolve eq440244 eq611767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440244
  have eq619084 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq617753
       grind)
    | exact superpose eq617753 eq44
    | exact resolve eq44 eq617753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq617753
  have eq619217 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq437010 eq619084
    | exact resolve eq619084 eq437010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437010 eq619084
  have eq619271 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq619217
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq619217
    | exact resolve eq619217 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq619217
  have eq619535 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq619271 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq619271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619271
  have eq619557 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq437019 eq619535
    | exact resolve eq619535 eq437019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619535
  have eq619583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq437019 eq619557
    | exact resolve eq619557 eq437019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619557
  have eq619606 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq619583
       have r₂ := eq27
       grind)
    | exact resolve eq619583 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619583
  have eq625262 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq619606 eq611767
    | exact resolve eq611767 eq619606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619606
  have eq627178 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq625262 eq609503
    | exact resolve eq609503 eq625262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609503 eq625262
  have eq633624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq627178 eq437019
    | exact resolve eq437019 eq627178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627178
  have eq633908 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq633624
       have r₂ := eq27
       grind)
    | exact resolve eq633624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633624
  have eq634178 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq633908 eq390
    | exact resolve eq390 eq633908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq633908
  have eq635755 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq634178 eq611767
    | exact resolve eq611767 eq634178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611767 eq634178
  have eq638841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq635755 eq437019
    | exact resolve eq437019 eq635755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437019 eq635755
  have eq639513 : False := by grind
  exact eq639513

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyx_pxy_Equation2536 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq85 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq85 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq119
  have eq123 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq122
  have eq162 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq647 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq659 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq659
    | exact resolve eq659 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq666 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq647 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq647
    | exact resolve eq647 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq673 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq663 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq663
    | (have j0 := eq663 x y
       grind)
    | exact resolve eq663 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq673 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq673
       grind)
    | exact resolve eq12 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq691
  have eq727 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X2 (M.op (M.op X2 X0) X3)) X0)) ∨ (M.op X0 X1) = (M.op (M.op X2 (M.op (M.op X2 X0) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq86 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq86
    | exact resolve eq86 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq741 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op (M.op X2 (M.op (M.op X2 X0) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq727 X0 X1 X2 X3
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq727
    | (have j0 := eq727 X0 X1 X2 X3
       grind)
    | exact resolve eq727 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq744 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq741
    | (have j0 := eq741 X0 X1 x x
       grind)
    | exact resolve eq741 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq817 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (M.op X2 (M.op (M.op X2 (σ X0)) X3)) (σ (k X0 X1))) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 (σ X0) X2 X3 (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq55
    | (have j1 := eq69 X0 X1
       grind)
    | exact resolve eq55 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq3548 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) X0)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq123 eq380
    | exact resolve eq380 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq3846 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0 x X0
       have i₂ := eq666 X0 X0 x
       grind)
    | exact superpose eq666 eq55
    | exact resolve eq55 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3890 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq666 X0 X0 X0
       have i₂ := eq3846 X0
       grind)
    | exact superpose eq3846 eq666
    | exact resolve eq666 eq3846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3892 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X0 X0 X1
       have i₂ := eq3846 X0
       grind)
    | exact superpose eq3846 eq55
    | exact resolve eq55 eq3846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq16316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq76 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq16316
    | exact resolve eq16316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16316
  have eq16328 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq16317
       have r₂ := eq28
       grind)
    | exact resolve eq16317 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16317
  have eq16478 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq16328 eq744
    | exact resolve eq744 eq16328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq16328
  have eq16480 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq16478
  have eq16488 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq16480 eq76
    | exact resolve eq76 eq16480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq16480
  have eq16502 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16488
  have eq16676 : y = (M.op (M.op (M.op y y) x) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3892 y x
       have i₂ := eq16502
       grind)
    | exact superpose eq16502 eq3892
    | exact resolve eq3892 eq16502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3892 eq16502
  have eq18004 : (M.op (M.op y y) x) = (M.op (M.op (M.op y y) y) (M.op (M.op y y) x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq666 (M.op y y) x y
       have i₂ := eq16676
       grind)
    | exact superpose eq16676 eq666
    | exact resolve eq666 eq16676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18032 : (M.op (M.op y y) x) = (M.op y (M.op (M.op y y) x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18004
       have i₂ := eq3846 y
       grind)
    | exact superpose eq3846 eq18004
    | exact resolve eq18004 eq3846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3846 eq18004
  have eq140895 : (M.op y y) = (M.op (M.op (M.op y y) x) (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq666 y y x
       have i₂ := eq18032
       grind)
    | exact superpose eq18032 eq666
    | exact resolve eq666 eq18032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq18032
  have eq197310 : x = (M.op (M.op (M.op y y) (M.op y y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 x (M.op y y) (M.op y y)
       have i₂ := eq140895
       grind)
    | exact superpose eq140895 eq14
    | exact resolve eq14 eq140895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140895
  have eq197364 : x = (M.op (M.op y y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq197310
       have i₂ := eq3890 y
       grind)
    | exact superpose eq3890 eq197310
    | exact resolve eq197310 eq3890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197310
  have eq197372 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16676
       have i₂ := eq197364
       grind)
    | exact superpose eq197364 eq16676
    | exact resolve eq16676 eq197364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16676 eq197364
  have eq197448 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq197372
  have eq197458 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq197448
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq197448
    | exact resolve eq197448 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197448
  have eq197462 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq197458 eq30
    | exact resolve eq30 eq197458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq197458
  have eq197617 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq197462
    | exact resolve eq197462 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197462
  have eq197618 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq197617
  have eq197638 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq197618 eq29
    | exact resolve eq29 eq197618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197650 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq197618 eq68
    | exact resolve eq68 eq197618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197618
  have eq198278 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq162 eq197650
    | exact resolve eq197650 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq197650
  have eq198289 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq197638
    | exact resolve eq197638 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197638
  have eq198308 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq198289 eq21
    | exact resolve eq21 eq198289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198385 : y = (k y x) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq198289 eq693
    | exact resolve eq693 eq198289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq198289
  have eq198888 : y = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq198385
  have eq199036 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq198308
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq198308
    | exact resolve eq198308 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198308
  have eq199069 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq199036 eq27
    | exact resolve eq27 eq199036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200968 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ y)) X1)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq817 y x X0 X1
       have i₂ := eq198888
       grind)
    | exact superpose eq198888 eq817
    | (have j0 := eq817 y x x x
       grind)
    | exact resolve eq817 eq198888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq198888
  have eq201000 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ y)) X1)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq200968 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq200968
    | (have j0 := eq200968 X0 X1
       grind)
    | exact resolve eq200968 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200968
  have eq201022 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq201000 x x
       have i₂ := eq14 sF3 x x
       grind)
    | exact superpose eq14 eq201000
    | exact resolve eq201000 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201000
  have eq201029 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq201022
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq201022
    | exact resolve eq201022 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201022
  have eq201033 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq201029
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq201029
    | exact resolve eq201029 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201029
  have eq201037 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq201033
    | exact resolve eq201033 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201033
  have eq201041 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq201037
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq201037
    | exact resolve eq201037 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201037
  have eq201045 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq201041
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq201041
    | exact resolve eq201041 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201041
  have eq201347 : y = (M.op (M.op x (M.op x x)) y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq198278 eq53
    | exact resolve eq53 eq198278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq198278
  have eq201457 : y = (M.op (M.op x x) y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq201347
       have i₂ := eq663 x x
       grind)
    | (have i₁ := eq201347
       have i₂ := eq663 x (M.op x x)
       grind)
    | exact superpose eq663 eq201347
    | exact resolve eq201347 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201347
  have eq239552 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op (M.op x y) (M.op x y))) X0)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3548 X0
       have i₂ := eq3890 sF0
       grind)
    | exact superpose eq3890 eq3548
    | exact resolve eq3548 eq3890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3548 eq3890
  have eq239553 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq123 eq239552
    | exact resolve eq239552 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq239552
  have eq239554 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq239553 X0
       have i₂ := eq663 (M.op sF1 sF1) (M.op (M.op sF1 sF1) X0)
       grind)
    | (have i₁ := eq239553 x
       have i₂ := eq663 (M.op sF1 sF1) x
       grind)
    | exact superpose eq663 eq239553
    | exact resolve eq239553 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq239553
  have eq455596 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq199036 eq201045
    | exact resolve eq201045 eq199036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199036 eq201045
  have eq455724 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq455596
  have eq455800 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq455724
       have r₂ := eq28
       grind)
    | exact resolve eq455724 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455724
  have eq455859 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq455800 eq239554
    | exact resolve eq239554 eq455800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239554
  have eq463265 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq455859 eq14
    | exact resolve eq14 eq455859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473305 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq455800 eq463265
    | exact resolve eq463265 eq455800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455800 eq463265
  have eq473564 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq473305 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473305
  have eq473624 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq473564 eq455859
    | exact resolve eq455859 eq473564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455859 eq473564
  have eq473935 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq473624 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473624
  have eq474396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq473935 eq199069
    | exact resolve eq199069 eq473935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199069 eq473935
  have eq474513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq474396
  have eq474600 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq474513
       have r₂ := eq28
       grind)
    | exact resolve eq474513 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474513
  have eq474651 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq474600 eq29
    | exact resolve eq29 eq474600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq474600
  have eq475641 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq474651
    | exact resolve eq474651 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq474651
  have eq475642 : x = (M.op x y) ∨ x = y := by grind
  clear eq475641
  have eq475740 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq475642 eq673
    | exact resolve eq673 eq475642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq477541 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq201457
       have i₂ := eq475740
       grind)
    | exact superpose eq475740 eq201457
    | exact resolve eq201457 eq475740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201457 eq475740
  have eq477699 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq477541
  have eq477803 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq477699
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq477699
    | exact resolve eq477699 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477699
  have eq477804 : y = (M.op x y) ∨ x = y := by grind
  clear eq477803
  have eq478394 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq477804 eq475642
    | exact resolve eq475642 eq477804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475642 eq477804
  have eq478395 : x = y := by grind
  clear eq478394
  have eq478944 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq478395
       grind)
    | exact superpose eq478395 eq19
    | exact resolve eq19 eq478395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq478945 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq478395
       grind)
    | exact superpose eq478395 eq25
    | exact resolve eq25 eq478395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq478395
  have eq479281 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq478945
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq478945
    | exact resolve eq478945 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq478945
  have eq479314 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq479281 eq27
    | exact resolve eq27 eq479281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq479281
  have eq479959 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq479314 eq68
    | exact resolve eq68 eq479314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq479314
  have eq480141 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq479959
       have i₂ := eq478944
       grind)
    | exact superpose eq478944 eq479959
    | exact resolve eq479959 eq478944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478944 eq479959
  have eq480151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq480141 eq15
    | exact resolve eq15 eq480141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480141
  have eq480675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq480151
    | exact resolve eq480151 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq480151
  have eq480820 : False := by grind
  exact eq480820

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq27 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (M.op X0 X0)
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq133 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (M.op (k (σ X1) X2) (σ X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (k (σ X1) X2)
       have i₂ := eq27 X1 X2 X0
       grind)
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ X0) (k (σ X1) X2)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq72
    | exact resolve eq72 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ x)
       have i₂ := eq72 x x
       grind)
    | exact superpose eq72 eq19
    | (have j1 := eq72 X0 X0
       grind)
    | exact resolve eq19 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (M.op X1 X1)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq9
    | (have j1 := eq72 X0 X0
       grind)
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq159 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (M.op X1 X1)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq161 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq150 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq217 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq67 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq66 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq66 eq67
    | exact resolve eq67 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq218 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq67 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq218
    | exact resolve eq218 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq225 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq217
    | exact resolve eq217 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq226 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq224 X0
       have i₂ := eq19 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq224
    | exact resolve eq224 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq227 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq226 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq226
    | exact resolve eq226 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq228 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq227 (M.op X0 X0)
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq227
    | exact resolve eq227 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq228 X0
       have i₂ := eq227 X0
       grind)
    | exact superpose eq227 eq228
    | exact resolve eq228 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq306 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq225 X0
       grind)
    | exact superpose eq225 eq9
    | exact resolve eq9 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq225 X0
       grind)
    | exact superpose eq225 eq9
    | exact resolve eq9 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X1) = (M.op (M.op X0 (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq306 X0 X2
       have i₂ := eq306 X0 X1
       grind)
    | exact superpose eq306 eq306
    | exact resolve eq306 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq225 X0
       grind)
    | exact superpose eq225 eq306
    | exact resolve eq306 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0
       have i₂ := eq306 X0 X1
       grind)
    | exact superpose eq306 eq65
    | exact resolve eq65 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X2
       have i₂ := eq306 X0 X1
       grind)
    | exact superpose eq306 eq67
    | exact resolve eq67 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq349 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq225 X0
       have i₂ := eq306 X0 X1
       grind)
    | exact superpose eq306 eq225
    | exact resolve eq225 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq227 X0
       have i₂ := eq306 X0 X1
       grind)
    | exact superpose eq306 eq227
    | exact resolve eq227 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0
       have i₂ := eq306 X0 X1
       grind)
    | exact superpose eq306 eq233
    | exact resolve eq233 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (k (σ (τ X0)) X0) (M.op X1 X1)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq159 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq159
    | (have j0 := eq159 (τ X0) X1
       grind)
    | exact resolve eq159 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq392 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X1 X1)) X1) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq395 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X1 X1)) X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq392 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq392
    | (have j0 := eq392 X0 X1
       grind)
    | exact resolve eq392 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq399 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq346 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq225 X0
       grind)
    | exact superpose eq225 eq346
    | exact resolve eq346 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq413 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq346 (M.op X0 X0) x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq346
    | exact resolve eq346 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 ∨ (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op X0 (M.op X1 X1)) X1) X0
       have i₂ := eq346 X0 X1
       grind)
    | exact superpose eq346 eq13
    | (have j0 := eq13 (M.op (M.op X0 (M.op X1 X1)) X1) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 (M.op X1 X1)) X1) X0
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq13 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 ∨ (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq418 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq423 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq420 X0 X1
       have i₂ := eq351 X0 X1
       grind)
    | exact superpose eq351 eq420
    | (have j0 := eq420 X0 X1
       grind)
    | exact resolve eq420 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq554 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq350 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq307 X0 X0
       grind)
    | exact superpose eq307 eq350
    | exact resolve eq350 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq638 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq307 X0 X0
       grind)
    | exact superpose eq307 eq351
    | exact resolve eq351 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X0 (M.op X1 X1)) X1) X0
       have i₂ := eq351 X0 X1
       grind)
    | exact superpose eq351 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq664 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1
       have i₂ := eq346 X0 X1
       grind)
    | exact superpose eq346 eq660
    | (have j0 := eq660 X0 X1
       grind)
    | exact resolve eq660 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq678 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq664 X0 X1
       have j1 := eq423 X0 X1
       grind)
    | (have r₁ := eq664 X0 X1
       have r₂ := eq423 X0 X1
       grind)
    | exact resolve eq664 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq664
  have eq700 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq678 (M.op X0 X0) x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq678
    | exact resolve eq678 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq776 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq700 (σ X0)
       grind)
    | exact superpose eq700 eq29
    | exact resolve eq29 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq700
  have eq1224 : ∀ X0 : G, (M.op (k (σ (τ X0)) X0) (σ (τ X0))) = (M.op (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq161 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq161
    | (have j0 := eq161 (τ X0)
       grind)
    | exact resolve eq161 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq1270 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1224 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1224
    | (have j0 := eq1224 X0
       grind)
    | exact resolve eq1224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1273 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1270 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1270
    | (have j0 := eq1270 X0
       grind)
    | exact resolve eq1270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1541 : ∀ X0 X1 X2 : G, (σ (σ X2)) = (M.op (k (σ (σ X0)) X1) (σ (σ X2))) ∨ (M.op (k (σ (σ X0)) X1) (σ (σ X2))) = (σ (σ (k (k X0 (τ (τ X1))) X2))) ∨ (σ (σ X2)) = (M.op (σ (σ X2)) (k (σ (σ X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq144 (σ X0) X1 (σ X2)
       have i₂ := eq28 X0 (τ X1) X2
       grind)
    | exact superpose eq28 eq144
    | (have j0 := eq144 (σ X0) X1 (σ X2)
       grind)
    | exact resolve eq144 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq144
  have eq2066 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq335 (M.op (M.op X1 X1) X1) (M.op X0 X1)
       have i₂ := eq335 X1 X0
       grind)
    | exact superpose eq335 eq335
    | exact resolve eq335 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2149 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1)) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2066 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq2066
    | exact resolve eq2066 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066
  have eq2173 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) X0) (M.op X1 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2149 X0 X1
       have i₂ := eq227 X1
       grind)
    | exact superpose eq227 eq2149
    | exact resolve eq2149 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2186 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2173 X0 X1
       have i₂ := eq233 X1
       grind)
    | exact superpose eq233 eq2173
    | exact resolve eq2173 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2476 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq346 (k X0 X0) x
       have i₂ := eq395 X0 x
       grind)
    | exact superpose eq395 eq346
    | (have j1 := eq395 X0 x
       grind)
    | exact resolve eq346 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq2511 : ∀ X0 : G, (M.op (M.op (k X0 X0) (M.op (M.op (k X0 X0) (k X0 X0)) (k X0 X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq399 (k X0 X0) X0
       have i₂ := eq2476 X0
       grind)
    | exact superpose eq2476 eq399
    | (have j1 := eq2476 X0
       grind)
    | exact resolve eq399 eq2476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq2476
  have eq2520 : ∀ X0 : G, (M.op (M.op (k X0 X0) (k X0 X0)) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2511 X0
       have i₂ := eq233 (k X0 X0)
       grind)
    | exact superpose eq233 eq2511
    | (have j0 := eq2511 X0
       grind)
    | exact resolve eq2511 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq2822 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq638 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq638
    | exact resolve eq638 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq4690 : ∀ X0 : G, (M.op (M.op (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2520 X0
       have i₂ := eq1273 X0
       grind)
    | exact superpose eq1273 eq2520
    | (have j0 := eq2520 X0
       have j1 := eq1273 X0
       grind)
    | exact resolve eq2520 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq4692 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq307 X0 (k X0 X0)
       have i₂ := eq2520 X0
       grind)
    | exact superpose eq2520 eq307
    | (have j1 := eq2520 X0
       grind)
    | exact resolve eq307 eq2520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520
  have eq4720 : ∀ X0 : G, (M.op (M.op (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4690 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4690
  have eq4743 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4692 X0
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq4692
    | (have j0 := eq4692 X0
       grind)
    | exact resolve eq4692 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4692
  have eq4756 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4743 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4743 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq4743 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4743
  have eq4797 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4756 (σ X0)
       grind)
    | exact superpose eq4756 eq15
    | exact resolve eq15 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4804 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq4756 (τ X0)
       grind)
    | exact superpose eq4756 eq33
    | exact resolve eq33 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq4817 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4804 X0
       have i₂ := eq4756 X0
       grind)
    | exact superpose eq4756 eq4804
    | exact resolve eq4804 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804
  have eq4823 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4797 X0
       have i₂ := eq4756 X0
       grind)
    | exact superpose eq4756 eq4797
    | exact resolve eq4797 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797
  have eq5022 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (τ (M.op X0 X0))) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq346 X1 (τ X0)
       have i₂ := eq4817 X0
       grind)
    | exact superpose eq4817 eq346
    | exact resolve eq346 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5113 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (σ (M.op X0 X0))) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq4823 X0
       grind)
    | exact superpose eq4823 eq9
    | exact resolve eq9 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5114 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0)
       have i₂ := eq4823 X0
       grind)
    | exact superpose eq4823 eq19
    | exact resolve eq19 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5151 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq346 X1 (σ X0)
       have i₂ := eq4823 X0
       grind)
    | exact superpose eq4823 eq346
    | exact resolve eq346 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq5158 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq413 (σ X0)
       have i₂ := eq4823 X0
       grind)
    | exact superpose eq4823 eq413
    | exact resolve eq413 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5205 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5114 X0
       have i₂ := eq4823 (M.op X0 X0)
       grind)
    | exact superpose eq4823 eq5114
    | exact resolve eq5114 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5114
  have eq5219 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5205 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq5205
    | exact resolve eq5205 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5205
  have eq6037 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5158 (M.op (M.op X0 X0) X0)
       have i₂ := eq307 X0 X0
       grind)
    | exact superpose eq307 eq5158
    | exact resolve eq5158 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6039 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq5158 (σ X0)
       have i₂ := eq4823 X0
       grind)
    | exact superpose eq4823 eq5158
    | exact resolve eq5158 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6468 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 (M.op X1 X1)) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6037 X0
       have i₂ := eq306 X0 X1
       grind)
    | exact superpose eq306 eq6037
    | exact resolve eq6037 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq10977 : ∀ X0 : G, (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) = (σ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5219 (σ X0)
       have i₂ := eq4823 X0
       grind)
    | exact superpose eq4823 eq5219
    | exact resolve eq5219 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11058 : ∀ X0 : G, (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) = (σ (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq10977 X0
       have i₂ := eq5219 X0
       grind)
    | exact superpose eq5219 eq10977
    | exact resolve eq10977 eq5219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5219 eq10977
  have eq12144 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6468 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6468
    | exact resolve eq6468 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6468
  have eq12295 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1))
       have i₂ := eq12144 X0 X1
       grind)
    | exact superpose eq12144 eq554
    | exact resolve eq554 eq12144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq12144
  have eq12342 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (σ (M.op (M.op (M.op (τ X0) (M.op X1 X1)) X1) (M.op (M.op (τ X0) (M.op X1 X1)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12295 X0 X1
       have i₂ := eq4823 (M.op (M.op (τ X0) (M.op X1 X1)) X1)
       grind)
    | exact superpose eq4823 eq12295
    | exact resolve eq12295 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12295
  have eq12376 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12342 X0 X1
       have i₂ := eq349 (τ X0) X1
       grind)
    | exact superpose eq349 eq12342
    | exact resolve eq12342 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12342
  have eq12385 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X0) = (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12376 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12376
    | exact resolve eq12376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12376
  have eq12393 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12385 X0 X1
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq12385
    | exact resolve eq12385 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12385
  have eq18069 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (M.op X0 X0))) ∨ (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) = (k (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ (σ (M.op X0 X0))) (σ (σ X0))
       have i₂ := eq6039 X0
       grind)
    | exact superpose eq6039 eq12
    | (have j0 := eq12 (σ (σ (M.op X0 X0))) (σ (σ X0))
       grind)
    | exact resolve eq12 eq6039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18090 : ∀ X0 : G, (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) = (σ (k (σ (M.op X0 X0)) (σ X0))) ∨ (σ (σ X0)) ≠ (σ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18069 X0
       have i₂ := eq15 (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact superpose eq15 eq18069
    | (have j0 := eq18069 X0
       grind)
    | exact resolve eq18069 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18069
  have eq18123 : ∀ X0 : G, (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (σ (σ X0)) ≠ (σ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18090 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq18090
    | (have j0 := eq18090 X0
       grind)
    | exact resolve eq18090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18090
  have eq18138 : ∀ X0 : G, (σ (σ (M.op (M.op X0 X0) X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (σ (σ X0)) ≠ (σ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18123 X0
       have i₂ := eq11058 X0
       grind)
    | exact superpose eq11058 eq18123
    | (have j0 := eq18123 X0
       grind)
    | exact resolve eq18123 eq11058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq29566 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6037 X0
       have i₂ := eq12393 X0 X1
       grind)
    | exact superpose eq12393 eq6037
    | exact resolve eq6037 eq12393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6037
  have eq50701 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29566 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29566
    | exact resolve eq29566 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29566
  have eq52779 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq348 X0 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have i₂ := eq334 (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X1 X1) X2
       grind)
    | (have i₁ := eq348 X0 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have i₂ := eq334 (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) X2 (M.op X1 X1)
       grind)
    | exact superpose eq334 eq348
    | exact resolve eq348 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq348
  have eq53474 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 (M.op (M.op X1 X1) X1)))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52779 X0 X1 X2
       have i₂ := eq2822 X1 X1
       grind)
    | exact superpose eq2822 eq52779
    | exact resolve eq52779 eq2822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822 eq52779
  have eq53715 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53474 X0 X1 X2
       have i₂ := eq233 X1
       grind)
    | exact superpose eq233 eq53474
    | exact resolve eq53474 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53474
  have eq53802 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X1) X1) (M.op X1 X1))) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53715 X0 X1 X2
       have i₂ := eq2186 X1 X1
       grind)
    | exact superpose eq2186 eq53715
    | exact resolve eq53715 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186 eq53715
  have eq53840 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53802 X0 X1 X2
       have i₂ := eq227 X1
       grind)
    | exact superpose eq227 eq53802
    | exact resolve eq53802 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53802
  have eq55466 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X2) (τ (M.op X0 X0))) (τ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53840 X1 X2 (τ X0)
       have i₂ := eq4817 X0
       grind)
    | exact superpose eq4817 eq53840
    | exact resolve eq53840 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55501 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (σ X1)) = (M.op (M.op (M.op X0 X0) (σ (M.op X1 X1))) (M.op (M.op X0 X0) (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53840 (M.op (M.op X0 X0) (σ (M.op X1 X1))) (σ X1) X0
       have i₂ := eq5151 X1 (M.op X0 X0)
       grind)
    | exact superpose eq5151 eq53840
    | exact resolve eq53840 eq5151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5151
  have eq55897 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (M.op (σ X0) X1) (M.op X2 X2)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4823 X0
       have i₂ := eq53840 (σ X0) X1 X2
       grind)
    | exact superpose eq53840 eq4823
    | exact resolve eq4823 eq53840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53840
  have eq148347 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X2) (k (σ X0) X1)
       have i₂ := eq133 X2 X0 X1
       grind)
    | exact superpose eq133 eq12
    | (have j0 := eq12 (σ X2) (k (σ X0) X1)
       have j1 := eq133 X2 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (k (σ X1) X2)
       have r₂ := eq133 X0 X1 X2
       grind)
    | exact resolve eq12 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq148381 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq148347 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148347
  have eq148399 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq148381 X0 X1 X2
       have i₂ := eq27 X0 X1 X2
       grind)
    | exact superpose eq27 eq148381
    | (have j0 := eq148381 X0 X1 X2
       grind)
    | exact resolve eq148381 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq148381
  have eq148400 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq148399 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148399
  have eq154062 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (τ (M.op (M.op (M.op (M.op (σ X0) X1) (M.op X2 X2)) X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq55897 X0 X1 X2
       grind)
    | exact superpose eq55897 eq10
    | exact resolve eq10 eq55897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55897
  have eq177254 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (M.op (k (σ (σ X0)) (σ (σ X0))) (σ (σ X0))) = (σ (σ (k (k X0 (τ (τ (σ (σ X0))))) X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq4720 (σ (σ X0))
       have i₂ := eq1541 X0 (σ (σ X0)) X0
       grind)
    | exact superpose eq1541 eq4720
    | (have j0 := eq4720 (σ (σ X0))
       have j1 := eq1541 X0 (σ (σ X0)) X0
       grind)
    | exact resolve eq4720 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541 eq4720
  have eq177299 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (M.op (k (σ (σ X0)) (σ (σ X0))) (σ (σ X0))) = (σ (σ (k (k X0 (τ (τ (σ (σ X0))))) X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have j0 := eq177254 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177254
  have eq177342 : ∀ X0 : G, (σ (σ X0)) = (σ (M.op (σ X0) (σ X0))) ∨ (M.op (k (σ (σ X0)) (σ (σ X0))) (σ (σ X0))) = (σ (σ (k (k X0 (τ (τ (σ (σ X0))))) X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177299 X0
       have i₂ := eq4823 (σ X0)
       grind)
    | exact superpose eq4823 eq177299
    | (have j0 := eq177299 X0
       grind)
    | exact resolve eq177299 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177299
  have eq177429 : ∀ X0 : G, (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (M.op (k (σ (σ X0)) (σ (σ X0))) (σ (σ X0))) = (σ (σ (k (k X0 (τ (τ (σ (σ X0))))) X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177342 X0
       have i₂ := eq4823 X0
       grind)
    | exact superpose eq4823 eq177342
    | (have j0 := eq177342 X0
       grind)
    | exact resolve eq177342 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177342
  have eq177479 : ∀ X0 : G, (M.op (k (σ (σ X0)) (σ (σ X0))) (σ (σ X0))) = (σ (σ (k (k X0 (τ (σ X0))) X0))) ∨ (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177429 X0
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq177429
    | (have j0 := eq177429 X0
       grind)
    | exact resolve eq177429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177429
  have eq177510 : ∀ X0 : G, (σ (σ (k (k X0 X0) X0))) = (M.op (k (σ (σ X0)) (σ (σ X0))) (σ (σ X0))) ∨ (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177479 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177479
    | (have j0 := eq177479 X0
       grind)
    | exact resolve eq177479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177479
  have eq177530 : ∀ X0 : G, (M.op (σ (k (σ X0) (σ X0))) (σ (σ X0))) = (σ (σ (k (k X0 X0) X0))) ∨ (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177510 X0
       have i₂ := eq15 (σ X0) (σ X0)
       grind)
    | exact superpose eq15 eq177510
    | (have j0 := eq177510 X0
       grind)
    | exact resolve eq177510 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177510
  have eq177543 : ∀ X0 : G, (M.op (σ (k (σ X0) (σ X0))) (σ (σ X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177530 X0
       have i₂ := eq4756 X0
       grind)
    | exact superpose eq4756 eq177530
    | (have j0 := eq177530 X0
       grind)
    | exact resolve eq177530 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177530
  have eq177555 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177543 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq177543
    | (have j0 := eq177543 X0
       grind)
    | exact resolve eq177543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177543
  have eq177567 : ∀ X0 : G, (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177555 X0
       have i₂ := eq4756 X0
       grind)
    | exact superpose eq4756 eq177555
    | (have j0 := eq177555 X0
       grind)
    | exact resolve eq177555 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177555
  have eq177579 : ∀ X0 : G, (σ (σ (M.op (M.op X0 X0) X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177567 X0
       have i₂ := eq11058 X0
       grind)
    | exact superpose eq11058 eq177567
    | (have j0 := eq177567 X0
       grind)
    | exact resolve eq177567 eq11058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11058 eq177567
  have eq177587 : ∀ X0 : G, (σ (σ (M.op (M.op X0 X0) X0))) = (σ (σ (k (M.op X0 X0) X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (k (σ (σ X0)) (σ (σ X0)))) := by
    intro X0
    first
    | (have j0 := eq177579 X0
       have j1 := eq18138 X0
       grind)
    | (have r₁ := eq177579 X0
       have r₂ := eq18138 X0
       grind)
    | exact resolve eq177579 eq18138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177579
  have eq177594 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (k (σ X0) (σ X0)))) ∨ (σ (σ (M.op (M.op X0 X0) X0))) = (σ (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq177587 X0
       have i₂ := eq15 (σ X0) (σ X0)
       grind)
    | exact superpose eq15 eq177587
    | (have j0 := eq177587 X0
       grind)
    | exact resolve eq177587 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177587
  have eq177600 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ (k X0 X0)))) ∨ (σ (σ (M.op (M.op X0 X0) X0))) = (σ (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq177594 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq177594
    | (have j0 := eq177594 X0
       grind)
    | exact resolve eq177594 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177594
  have eq177606 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ (M.op X0 X0)))) ∨ (σ (σ (M.op (M.op X0 X0) X0))) = (σ (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq177600 X0
       have i₂ := eq4756 X0
       grind)
    | exact superpose eq4756 eq177600
    | (have j0 := eq177600 X0
       grind)
    | exact resolve eq177600 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4756 eq177600
  have eq177609 : ∀ X0 : G, (σ (σ X0)) = (σ (σ (M.op X0 X0))) ∨ (σ (σ (M.op (M.op X0 X0) X0))) = (σ (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq177606 X0
       have i₂ := eq6039 X0
       grind)
    | exact superpose eq6039 eq177606
    | (have j0 := eq177606 X0
       grind)
    | exact resolve eq177606 eq6039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6039 eq177606
  have eq177611 : ∀ X0 : G, (σ (σ (M.op (M.op X0 X0) X0))) = (σ (σ (k (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq177609 X0
       have j1 := eq18138 X0
       grind)
    | (have r₁ := eq177609 X0
       have r₂ := eq18138 X0
       grind)
    | exact resolve eq177609 eq18138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18138 eq177609
  have eq177678 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (τ (σ (σ (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq10 (σ (k (M.op X0 X0) X0))
       have i₂ := eq177611 X0
       grind)
    | exact superpose eq177611 eq10
    | exact resolve eq10 eq177611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177728 : ∀ X0 : G, (τ (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0))))) = (k (σ (k (M.op X0 X0) X0)) (τ (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0
    first
    | (have i₁ := eq776 (σ (k (M.op X0 X0) X0))
       have i₂ := eq177611 X0
       grind)
    | exact superpose eq177611 eq776
    | exact resolve eq776 eq177611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq177611
  have eq177908 : ∀ X0 : G, (τ (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))))) = (k (σ (k (M.op X0 X0) X0)) (τ (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0
    first
    | (have i₁ := eq177728 X0
       have i₂ := eq4823 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq4823 eq177728
    | exact resolve eq177728 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177728
  have eq177938 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq177678 X0
       have i₂ := eq10 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq10 eq177678
    | exact resolve eq177678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177678
  have eq178024 : ∀ X0 : G, (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) = (k (σ (k (M.op X0 X0) X0)) (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq177908 X0
       have i₂ := eq10 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq10 eq177908
    | exact resolve eq177908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177908
  have eq178095 : ∀ X0 : G, (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) = (k (σ (k (M.op X0 X0) X0)) (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq178024 X0
       have i₂ := eq4823 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq4823 eq178024
    | exact resolve eq178024 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178024
  have eq178146 : ∀ X0 : G, (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) = (σ (k (k (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq178095 X0
       have i₂ := eq15 (k (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq15 eq178095
    | exact resolve eq178095 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178095
  have eq178179 : ∀ X0 : G, (σ (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) = (σ (k (k (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq178146 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq178146
    | exact resolve eq178146 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq178146
  have eq178195 : ∀ X0 : G, (σ X0) = (σ (k (k (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq178179 X0
       have i₂ := eq227 X0
       grind)
    | exact superpose eq227 eq178179
    | exact resolve eq178179 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178179
  have eq178312 : ∀ X0 : G, (τ (σ X0)) = (k (k (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k (M.op X0 X0) X0) X0)
       have i₂ := eq178195 X0
       grind)
    | exact superpose eq178195 eq10
    | exact resolve eq10 eq178195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178313 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (k (k (M.op X0 X0) X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (k (M.op X0 X0) X0) X0) X1
       have i₂ := eq178195 X0
       grind)
    | exact superpose eq178195 eq15
    | exact resolve eq15 eq178195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178195
  have eq178519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k (k (M.op X0 X0) X0) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq178313 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq178313
    | exact resolve eq178313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178313
  have eq178520 : ∀ X0 : G, (k (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178312 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq178312
    | exact resolve eq178312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178312
  have eq179626 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op X0 X0) X0)
       have i₂ := eq177938 X0
       grind)
    | exact superpose eq177938 eq10
    | exact resolve eq10 eq177938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177938
  have eq179891 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq179626 X0
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq179626
    | exact resolve eq179626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179626
  have eq180682 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq179891 (M.op X0 X0)
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq179891
    | exact resolve eq179891 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq180688 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq179891 (M.op (M.op X0 X0) X0)
       have i₂ := eq307 X0 X0
       grind)
    | exact superpose eq307 eq179891
    | exact resolve eq179891 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq179891
  have eq180827 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq180688 X0
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq180688
    | exact resolve eq180688 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180688
  have eq180832 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq180682 X0
       have i₂ := eq227 X0
       grind)
    | exact superpose eq227 eq180682
    | exact resolve eq180682 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq180682
  have eq181058 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X1) (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq180827 X0
       have i₂ := eq335 X1 X0
       grind)
    | exact superpose eq335 eq180827
    | exact resolve eq180827 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq180827
  have eq181926 : ∀ X0 X1 : G, (k (σ (M.op (M.op (τ X0) (M.op X1 X1)) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq180832 X0
       have i₂ := eq12393 X0 X1
       grind)
    | exact superpose eq12393 eq180832
    | exact resolve eq180832 eq12393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393 eq180832
  have eq201532 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1)))) = (k (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq181058 (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) X0
       have i₂ := eq50701 X0 X1
       grind)
    | exact superpose eq50701 eq181058
    | exact resolve eq181058 eq50701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50701 eq181058
  have eq201973 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1)))) = (k (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq201532 X0 X1
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq201532
    | exact resolve eq201532 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq201532
  have eq202324 : ∀ X0 X1 : G, (σ (M.op (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1)) (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1)))) = (k (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq201973 X0 X1
       have i₂ := eq4823 (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))
       grind)
    | exact superpose eq4823 eq201973
    | exact resolve eq201973 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201973
  have eq202622 : ∀ X0 X1 : G, (σ (σ (M.op (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1) (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1)))) = (k (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202324 X0 X1
       have i₂ := eq4823 (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1)
       grind)
    | exact superpose eq4823 eq202324
    | exact resolve eq202324 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4823 eq202324
  have eq202836 : ∀ X0 X1 : G, (σ (σ (τ (τ X0)))) = (k (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202622 X0 X1
       have i₂ := eq349 (τ (τ X0)) X1
       grind)
    | exact superpose eq349 eq202622
    | exact resolve eq202622 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq202622
  have eq202958 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202836 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq202836
    | exact resolve eq202836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202836
  have eq203034 : ∀ X0 X1 : G, (k (σ (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1))) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq202958 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq202958
    | exact resolve eq202958 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202958
  have eq213333 : ∀ X0 X1 : G, (τ X0) = (k (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq181926 (τ X0) X1
       have i₂ := eq4817 X0
       grind)
    | exact superpose eq4817 eq181926
    | exact resolve eq181926 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181926
  have eq266103 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op (M.op (M.op (σ (τ X0)) X1) (M.op X2 X2)) X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4817 X0
       have i₂ := eq154062 (τ X0) X1 X2
       grind)
    | exact superpose eq154062 eq4817
    | exact resolve eq4817 eq154062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4817
  have eq266527 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq266103 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq266103
    | exact resolve eq266103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266103
  have eq353914 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (M.op X0 (M.op X2 X2)) X2) (σ X1))) = (τ (M.op (M.op (M.op X0 X0) (σ (M.op X1 X1))) (M.op (M.op X0 X0) (σ (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq266527 (M.op (M.op X0 X0) (σ (M.op X1 X1))) (σ X1) X2
       have i₂ := eq5113 X1 X0
       grind)
    | exact superpose eq5113 eq266527
    | exact resolve eq266527 eq5113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5113 eq266527
  have eq355782 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (M.op X0 X0) X0) (σ X1))) = (τ (M.op (M.op (M.op X0 (M.op X2 X2)) X2) (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq353914 X0 X1 X2
       have i₂ := eq55501 X0 X1
       grind)
    | exact superpose eq55501 eq353914
    | exact resolve eq353914 eq55501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55501 eq353914
  have eq727885 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (k (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1)) (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq148400 (σ (M.op (M.op (τ (τ X0)) (M.op X1 X1)) X1)) (M.op X0 X0) X2
       have i₂ := eq203034 X0 X1
       grind)
    | exact superpose eq203034 eq148400
    | exact resolve eq148400 eq203034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148400 eq203034
  have eq728137 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq727885 X0 x X2
       have i₂ := eq213333 X0 x
       grind)
    | exact superpose eq213333 eq727885
    | (have j0 := eq727885 X0 x X2
       grind)
    | exact resolve eq727885 eq213333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213333 eq727885
  have eq728346 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (k (σ X2) X0) ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq728137 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq728137
    | (have j0 := eq728137 X0 X2
       grind)
    | exact resolve eq728137 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq728137
  have eq728593 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq728346 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq728346
    | exact resolve eq728346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728770 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq728346 (σ X1) X0
       grind)
    | exact superpose eq728346 eq15
    | (have j1 := eq728346 (σ X1) X0
       grind)
    | exact resolve eq15 eq728346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728346
  have eq730100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (k (k (M.op X0 X0) X0) X0) X1)) ∨ (M.op (k (k (M.op X0 X0) X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178519 X0 X1
       have i₂ := eq728593 (k (k (M.op X0 X0) X0) X0) X1
       grind)
    | exact superpose eq728593 eq178519
    | (have j1 := eq728593 (k (k (M.op X0 X0) X0) X0) X1
       grind)
    | exact resolve eq178519 eq728593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178519 eq728593
  have eq730425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op (k (k (M.op X0 X0) X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq730100 X0 X1
       have i₂ := eq178520 X0
       grind)
    | exact superpose eq178520 eq730100
    | (have j0 := eq730100 X0 X1
       grind)
    | exact resolve eq730100 eq178520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730100
  have eq730521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq730425 X0 X1
       have i₂ := eq178520 X0
       grind)
    | exact superpose eq178520 eq730425
    | (have j0 := eq730425 X0 X1
       grind)
    | exact resolve eq730425 eq178520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178520 eq730425
  have eq1373553 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq728770 x y
       grind)
    | exact superpose eq728770 eq16
    | (have j1 := eq728770 x y
       grind)
    | exact resolve eq16 eq728770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728770
  have eq1393681 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1373553
       have i₂ := eq730521 x y
       grind)
    | exact superpose eq730521 eq1373553
    | (have j1 := eq730521 (σ x) (σ y)
       grind)
    | (have r₁ := eq1373553
       have r₂ := eq730521 x y
       grind)
    | exact resolve eq1373553 eq730521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730521 eq1373553
  have eq1393684 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1393681
  have eq1397344 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y (τ (M.op X0 X0))) (τ X0)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55466 X0 x y
       have i₂ := eq1393684
       grind)
    | exact superpose eq1393684 eq55466
    | exact resolve eq55466 eq1393684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55466 eq1393684
  have eq1397404 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1397344 x
       have i₂ := eq5022 x y
       grind)
    | exact superpose eq5022 eq1397344
    | exact resolve eq1397344 eq5022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5022 eq1397344
  have eq1397500 : ∀ X0 : G, (M.op x x) = (τ (M.op (M.op (M.op (σ y) (M.op X0 X0)) X0) (σ y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq154062 x (σ y) X0
       have i₂ := eq1397404
       grind)
    | exact superpose eq1397404 eq154062
    | exact resolve eq154062 eq1397404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154062 eq1397404
  have eq1397702 : (M.op x x) = (τ (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1397500 x
       have i₂ := eq355782 (σ y) y x
       grind)
    | exact superpose eq355782 eq1397500
    | exact resolve eq1397500 eq355782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355782 eq1397500
  have eq1397813 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1397702
       have i₂ := eq65 (σ y)
       grind)
    | exact superpose eq65 eq1397702
    | exact resolve eq1397702 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1397702
  have eq1397893 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1397813
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1397813
    | exact resolve eq1397813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397813
  have eq1397894 : y = (M.op x x) := by grind
  clear eq1397893
  have eq1401394 : y = (M.op x y) := by
    first
    | (have i₁ := eq413 x
       have i₂ := eq1397894
       grind)
    | exact superpose eq1397894 eq413
    | exact resolve eq413 eq1397894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq1401619 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5158 x
       have i₂ := eq1397894
       grind)
    | exact superpose eq1397894 eq5158
    | exact resolve eq5158 eq1397894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158 eq1397894
  have eq1439524 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1401619
       grind)
    | exact superpose eq1401619 eq16
    | exact resolve eq16 eq1401619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401619
  have eq1439758 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1439524
       have i₂ := eq1401394
       grind)
    | exact superpose eq1401394 eq1439524
    | exact resolve eq1439524 eq1401394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401394 eq1439524
  have eq1439759 : False := by grind
  exact eq1439759

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_pyx_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
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
  clear eq23
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
  clear eq25 eq36
  have eq51 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq371 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2881 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq375 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq375
    | exact resolve eq375 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq2886 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2881 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq2881
    | exact resolve eq2881 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881
  have eq2888 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2886 X0
       have i₂ := eq51 (M.op X0 X0)
       grind)
    | exact superpose eq51 eq2886
    | exact resolve eq2886 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2886
  have eq2889 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2888 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq2888
    | exact resolve eq2888 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2888
  have eq2890 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2889 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq2889
    | exact resolve eq2889 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2894 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2890 X0
       have i₂ := eq2889 X0
       grind)
    | exact superpose eq2889 eq2890
    | exact resolve eq2890 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq3009 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq2889 X0
       grind)
    | exact superpose eq2889 eq371
    | exact resolve eq371 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq2889
  have eq3013 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq14
    | exact resolve eq14 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3014 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq14
    | exact resolve eq14 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11729 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0
       have i₂ := eq3013 X0 X1
       grind)
    | exact superpose eq3013 eq372
    | exact resolve eq372 eq3013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq3013
  have eq11759 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11729 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq11729
    | exact resolve eq11729 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009
  have eq11773 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11729 (M.op X0 X0) x
       have i₂ := eq14 X0 x
       grind)
    | exact superpose eq14 eq11729
    | exact resolve eq11729 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11729
  have eq14831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq14831
    | exact resolve eq14831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14831
  have eq14843 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq14832
       have r₂ := eq28
       grind)
    | exact resolve eq14832 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14832
  have eq14874 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14843 eq11773
    | exact resolve eq11773 eq14843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14843
  have eq14877 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq14874
  have eq14897 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14877 eq11759
    | exact resolve eq11759 eq14877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14877
  have eq14900 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14897
       have i₂ := eq2894 sF2
       grind)
    | exact superpose eq2894 eq14897
    | exact resolve eq14897 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14897
  have eq14901 : (σ x) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (σ y))) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14900 eq3014
    | exact resolve eq3014 eq14900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14900
  have eq14907 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14901
       have i₂ := eq2894 sF3
       grind)
    | exact superpose eq2894 eq14901
    | exact resolve eq14901 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14901
  have eq15155 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq14907
  have eq15197 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq15155
    | exact resolve eq15155 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15155
  have eq15543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15197 eq86
    | exact resolve eq86 eq15197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq15197
  have eq15552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq15543
  have eq15554 : x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq15552
       have r₂ := eq28
       grind)
    | exact resolve eq15552 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15552
  have eq15585 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11773 y
       have i₂ := eq15554
       grind)
    | exact superpose eq15554 eq11773
    | exact resolve eq11773 eq15554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15554
  have eq15588 : x = (M.op y x) := by grind
  clear eq15585
  have eq15608 : y = (M.op (M.op x (M.op (M.op x x) x)) y) := by
    first
    | (have i₁ := eq11759 x y
       have i₂ := eq15588
       grind)
    | exact superpose eq15588 eq11759
    | exact resolve eq11759 eq15588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15588
  have eq15611 : y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq15608
       have i₂ := eq2894 x
       grind)
    | exact superpose eq2894 eq15608
    | exact resolve eq15608 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15608
  have eq15612 : x = (M.op y (M.op (M.op y y) y)) := by
    first
    | (have i₁ := eq3014 y x
       have i₂ := eq15611
       grind)
    | exact superpose eq15611 eq3014
    | exact resolve eq3014 eq15611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15611
  have eq15618 : x = (M.op y y) := by
    first
    | (have i₁ := eq15612
       have i₂ := eq2894 y
       grind)
    | exact superpose eq2894 eq15612
    | exact resolve eq15612 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15612
  have eq15870 : (M.op x y) = (k x y) := by grind
  clear eq15618
  have eq15912 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq15870
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15870
    | exact resolve eq15870 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15870
  have eq16365 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq15912
       grind)
    | exact superpose eq15912 eq45
    | exact resolve eq45 eq15912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq15912
  have eq16385 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16365
    | exact resolve eq16365 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16365
  have eq16520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16385 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq16385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16521 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq16520
    | exact resolve eq16520 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16520
  have eq16532 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq16521
       have r₂ := eq28
       grind)
    | exact resolve eq16521 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16521
  have eq17799 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq16532 eq11773
    | exact resolve eq11773 eq16532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11773 eq16532
  have eq17805 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq17799
  have eq17828 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) (σ y)) := by
    first
    | exact superpose eq17805 eq11759
    | exact resolve eq11759 eq17805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11759 eq17805
  have eq17832 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq17828
       have i₂ := eq2894 sF2
       grind)
    | exact superpose eq2894 eq17828
    | exact resolve eq17828 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17828
  have eq17927 : (σ x) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq17832 eq3014
    | exact resolve eq3014 eq17832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014 eq17832
  have eq17933 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17927
       have i₂ := eq2894 sF3
       grind)
    | exact superpose eq2894 eq17927
    | exact resolve eq17927 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894 eq17927
  have eq17940 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq17933
  have eq17998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16385 eq17940
    | exact resolve eq17940 eq16385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16385 eq17940
  have eq18005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17998
    | exact resolve eq17998 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17998
  have eq18008 : False := by grind
  exact eq18008

/-- `Equation2656`: `x = ((x ◇ x) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_y_pxy_Equation2656 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2656 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2656.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq47 : (σ (k x (k x x))) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq36
    | exact resolve eq36 eq44
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) (M.op X2 X3)) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X0 X0) (M.op X1 X2)) X1) = (M.op X1 (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X0) (M.op X1 X2)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X0) (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) (M.op X0 X2)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq97 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq108 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq168 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq216 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq52 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq287 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq420 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq287 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq287
    | exact resolve eq287 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq473 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
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
  have eq474 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X1) X1 X2 x
       have i₂ := eq54 X1 X1
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X2 X2) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 X1 (M.op (M.op X0 X0) (M.op x x)) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op x x))
       have i₂ := eq53 X0 X1 x x
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X0 X1)) X0) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq745 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1409 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) X0)
       have i₂ := eq541 X0 X0 X0
       grind)
    | exact superpose eq541 eq51
    | exact resolve eq51 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1410 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) X0)
       have i₂ := eq541 X0 X0 X0
       grind)
    | exact superpose eq541 eq52
    | exact resolve eq52 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1627 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq473 X0
       have i₂ := eq1409 X0
       grind)
    | exact superpose eq1409 eq473
    | exact resolve eq473 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1654 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x x) x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1409 eq474
    | exact resolve eq474 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1665 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq474 eq1654
    | exact resolve eq1654 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq1698 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq51 eq1627
    | exact resolve eq1627 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1627
  have eq1892 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1410 eq474
    | exact resolve eq474 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1903 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq474 eq1892
    | exact resolve eq1892 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq1892
  have eq5499 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq614 X0 X1
       have i₂ := eq565 X0 (M.op X0 X1)
       grind)
    | exact superpose eq565 eq614
    | exact resolve eq614 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq5530 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5499 (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op x x))
       have i₂ := eq535 X0 x x
       grind)
    | exact superpose eq535 eq5499
    | exact resolve eq5499 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq5499
  have eq5636 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5530 X0
       have i₂ := eq541 X0 X0 X0
       grind)
    | exact superpose eq541 eq5530
    | exact resolve eq5530 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5530
  have eq5797 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq5636 (M.op (M.op X0 X0) X0)
       have i₂ := eq541 X0 X0 X0
       grind)
    | exact superpose eq541 eq5636
    | exact resolve eq5636 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq5805 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5636 X0
       have i₂ := eq1409 X0
       grind)
    | exact superpose eq1409 eq5636
    | exact resolve eq5636 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5636
  have eq5821 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5797 X0
       have i₂ := eq565 X0 X0
       grind)
    | exact superpose eq565 eq5797
    | exact resolve eq5797 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5797
  have eq5923 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq168 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq168
    | (have j0 := eq168 x
       grind)
    | exact resolve eq168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq5948 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5923
  have eq5955 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5948
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5948
    | exact resolve eq5948 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5948
  have eq5963 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5955
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5955 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5955
  have eq5969 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5963 eq50
    | exact resolve eq50 eq5963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq7235 : (σ (k x (k x x))) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5963 eq47
    | exact resolve eq47 eq5963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq7236 : (σ (k x (k x x))) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq7235
       have i₂ := eq5821 sF2
       grind)
    | exact superpose eq5821 eq7235
    | exact resolve eq7235 eq5821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7235
  have eq7237 : (σ (k x (k x x))) = (M.op (M.op (σ x) (M.op x y)) x) := by
    first
    | (have i₁ := eq7236
       have i₂ := eq1409 sF2
       grind)
    | exact superpose eq1409 eq7236
    | exact resolve eq7236 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7236
  have eq17260 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5963 eq108
    | exact resolve eq108 eq5963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq5963
  have eq17365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17365
    | exact resolve eq17365 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17365
  have eq17374 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17366
       have r₂ := eq28
       grind)
    | exact resolve eq17366 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17366
  have eq17376 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17374
    | exact resolve eq17374 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17374
  have eq17380 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq17376
  have eq17478 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17380
    | exact resolve eq17380 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17380
  have eq17479 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq17478
  have eq18070 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17479 eq58
    | exact resolve eq58 eq17479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq18071 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17479 eq113
    | exact resolve eq113 eq17479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17479
  have eq18083 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18071
  have eq18089 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq18070
    | exact resolve eq18070 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18070
  have eq18093 : y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq18126 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5821 y
       have i₂ := eq18083
       grind)
    | exact superpose eq18083 eq5821
    | exact resolve eq5821 eq18083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18083
  have eq18178 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18126
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18126
    | exact resolve eq18126 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18126
  have eq18194 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18093
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18093
    | exact resolve eq18093 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18093
  have eq18195 : y = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18194
  have eq18554 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq18178
       grind)
    | exact superpose eq18178 eq73
    | exact resolve eq73 eq18178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18178
  have eq18576 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18554
    | exact resolve eq18554 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18554
  have eq18758 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq745 x y
       have i₂ := eq18195
       grind)
    | exact superpose eq18195 eq745
    | (have j0 := eq745 x y
       grind)
    | exact resolve eq745 eq18195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18195
  have eq18761 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18758
  have eq18764 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18761
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18761
    | exact resolve eq18761 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18761
  have eq18775 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18764
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18764
    | exact resolve eq18764 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18764
  have eq18781 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18775
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18775
    | exact resolve eq18775 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18775
  have eq18785 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18781
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18781
    | exact resolve eq18781 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18781
  have eq18789 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18785
    | exact resolve eq18785 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18785
  have eq18790 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18789
  have eq18928 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18790 eq5821
    | exact resolve eq5821 eq18790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18790
  have eq18978 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq18928
    | exact resolve eq18928 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18928
  have eq19215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18978 eq18576
    | exact resolve eq18576 eq18978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18576 eq18978
  have eq19221 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19215
  have eq19223 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19221
       have r₂ := eq28
       grind)
    | exact resolve eq19221 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19221
  have eq19226 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ y)) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19223 eq52
    | exact resolve eq52 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq19255 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19223 eq1903
    | exact resolve eq1903 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19264 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq19255
    | exact resolve eq19255 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19255
  have eq19269 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19264 eq5969
    | exact resolve eq5969 eq19264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19271 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq19264 eq14
    | exact resolve eq14 eq19264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19305 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op x y)) x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19264 eq5805
    | exact resolve eq5805 eq19264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5805
  have eq19362 : (M.op (M.op (σ x) (M.op x y)) x) = (σ (k x (τ (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7237
       have i₂ := eq19269
       grind)
    | exact superpose eq19269 eq7237
    | exact resolve eq7237 eq19269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7237
  have eq19400 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op x y)) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19362
       have i₂ := eq43 sF4
       grind)
    | exact superpose eq43 eq19362
    | exact resolve eq19362 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq19362
  have eq20387 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19264 eq19226
    | exact resolve eq19226 eq19264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19226 eq19264
  have eq20438 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq20387
  have eq20468 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19223 eq20438
    | exact resolve eq20438 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20507 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq20468
  have eq20526 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (M.op X0 X1))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq20507 eq53
    | exact resolve eq53 eq20507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq20507
  have eq20575 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20526 x x
       have i₂ := eq565 sF2 (M.op x x)
       grind)
    | exact superpose eq565 eq20526
    | exact resolve eq20526 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq20526
  have eq20588 : (τ (σ y)) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20575 eq5969
    | exact resolve eq5969 eq20575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5969
  have eq20615 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (M.op x y)) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20575 eq1409
    | exact resolve eq1409 eq20575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq20575
  have eq20678 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq20588
    | exact resolve eq20588 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20588
  have eq20872 : y = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19269
       have i₂ := eq20678
       grind)
    | exact superpose eq20678 eq19269
    | exact resolve eq19269 eq20678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19269 eq20678
  have eq20889 : y = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq20872
  have eq20957 : ∀ X0 : G, (k y (τ X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20889 eq420
    | exact resolve eq420 eq20889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq20889
  have eq20969 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20957 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq20957
    | exact resolve eq20957 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq20957
  have eq23582 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20438 eq19271
    | exact resolve eq19271 eq20438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19271 eq20438
  have eq23737 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq23582
  have eq24955 : (σ x) = (k (M.op (σ x) (σ y)) (k (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19400 eq19305
    | exact resolve eq19305 eq19400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19305
  have eq25006 : (σ x) = (k (M.op (σ x) (σ y)) (k (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq24955
  have eq27835 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19223 eq23737
    | exact resolve eq23737 eq19223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19223 eq23737
  have eq27885 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq27835
  have eq31292 : (M.op (σ y) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20615 eq19400
    | exact resolve eq19400 eq20615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19400 eq20615
  have eq31347 : (M.op (σ y) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq31292
  have eq35657 : (τ (σ x)) = (τ (k (σ y) (k (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25006 eq20969
    | exact resolve eq20969 eq25006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20969 eq25006
  have eq35729 : (τ (σ x)) = (τ (k (σ y) (k (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq35657
  have eq35784 : x = (τ (k (σ y) (k (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq35729
    | exact resolve eq35729 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35729
  have eq35798 : x = (τ (k (σ y) (M.op (σ y) (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31347 eq35784
    | exact resolve eq35784 eq31347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31347 eq35784
  have eq35860 : x = (τ (k (σ y) (M.op (σ y) (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq35798
  have eq51558 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18089
       grind)
    | exact superpose eq18089 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18089
  have eq51559 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq51558
  have eq51565 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51559
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51559
    | exact resolve eq51559 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51559
  have eq51566 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq51565
  have eq51596 : y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq51647 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5821 y
       have i₂ := eq51566
       grind)
    | exact superpose eq51566 eq5821
    | exact resolve eq5821 eq51566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51566
  have eq51714 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51647
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51647
    | exact resolve eq51647 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51647
  have eq51743 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51596
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51596
    | exact resolve eq51596 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51596
  have eq51744 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq51743
  have eq53428 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq51714
       grind)
    | exact superpose eq51714 eq73
    | exact resolve eq73 eq51714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq51714
  have eq53454 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq53428
    | exact resolve eq53428 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53428
  have eq54175 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq745 x y
       have i₂ := eq51744
       grind)
    | exact superpose eq51744 eq745
    | (have j0 := eq745 x y
       grind)
    | exact resolve eq745 eq51744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51744
  have eq54178 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54175
  have eq54183 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54178
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq54178
    | exact resolve eq54178 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54178
  have eq54196 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54183
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54183
    | exact resolve eq54183 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54183
  have eq54202 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54196
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq54196
    | exact resolve eq54196 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54196
  have eq54206 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54202
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54202
    | exact resolve eq54202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54202
  have eq54210 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq54206
    | exact resolve eq54206 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54206
  have eq54211 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq54210
  have eq54799 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54211 eq5821
    | exact resolve eq5821 eq54211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5821 eq54211
  have eq54906 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq54799
    | exact resolve eq54799 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54799
  have eq55628 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54906 eq53454
    | exact resolve eq53454 eq54906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53454 eq54906
  have eq55634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq55628
  have eq55638 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq55634
       have r₂ := eq28
       grind)
    | exact resolve eq55634 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55634
  have eq55640 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55638 eq28
    | exact resolve eq28 eq55638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55642 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55638 eq65
    | (have r₁ := eq65
       have r₂ := eq55638
       grind)
    | exact resolve eq65 eq55638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq55644 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55638 eq216
    | exact resolve eq216 eq55638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq55678 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55638 eq1903
    | exact resolve eq1903 eq55638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq55930 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq55642
  have eq55946 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq55678
    | exact resolve eq55678 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55678
  have eq55989 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq55946
  have eq56376 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55644 eq27885
    | exact resolve eq27885 eq55644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27885 eq55644
  have eq56521 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq56376
  have eq56555 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq56521
       have r₂ := eq55640
       grind)
    | exact resolve eq56521 eq55640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56521
  have eq56559 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56555
       have i₂ := eq54 sF3 sF2
       grind)
    | exact superpose eq54 eq56555
    | exact resolve eq56555 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56555
  have eq56571 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55930 eq113
    | exact resolve eq113 eq55930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq55930
  have eq56631 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq56571
  have eq204505 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55638 eq55989
    | exact resolve eq55989 eq55638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55638 eq55989
  have eq204546 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq204505
  have eq204623 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq56631 eq56559
    | exact resolve eq56559 eq56631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56559 eq56631
  have eq204795 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq204623
  have eq205971 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204546 eq80
    | exact resolve eq80 eq204546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204546
  have eq206013 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq205971
    | exact resolve eq205971 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq205971
  have eq209202 : x = (τ (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206013 eq35860
    | exact resolve eq35860 eq206013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35860 eq206013
  have eq209395 : x = (τ (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq209202
  have eq209494 : x = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq209395
       have r₂ := eq55640
       grind)
    | exact resolve eq209395 eq55640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55640 eq209395
  have eq209541 : x = (k y x) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq80 eq209494
    | exact resolve eq209494 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq209494
  have eq209542 : x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq209541
  have eq209586 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq209542
       grind)
    | exact superpose eq209542 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq209542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209587 : y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq209586
  have eq239526 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1698 x
       have i₂ := eq209587
       grind)
    | exact superpose eq209587 eq1698
    | exact resolve eq1698 eq209587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209587
  have eq239700 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq239526
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq239526
    | exact resolve eq239526 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239526
  have eq239701 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq239700
  have eq239728 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq239701
       grind)
    | exact superpose eq239701 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq239701
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq239701
       grind)
    | exact resolve eq13 eq239701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239701
  have eq239818 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq239728
  have eq239867 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq239818
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq239818
    | exact resolve eq239818 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239818
  have eq240185 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq209542
       have i₂ := eq239867
       grind)
    | exact superpose eq239867 eq209542
    | exact resolve eq209542 eq239867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209542 eq239867
  have eq240200 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq240185
  have eq240240 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq240200 eq21
    | exact resolve eq21 eq240200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240334 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq240200 eq1665
    | exact resolve eq1665 eq240200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665 eq240200
  have eq240557 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq240334
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq240334
    | exact resolve eq240334 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240334
  have eq240612 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq240240
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq240240
    | exact resolve eq240240 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240240
  have eq240622 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq240612 eq27
    | exact resolve eq27 eq240612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240612
  have eq242420 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17260
       have i₂ := eq240557
       grind)
    | exact superpose eq240557 eq17260
    | exact resolve eq17260 eq240557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17260 eq240557
  have eq242599 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq242420
  have eq242660 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq242599
    | exact resolve eq242599 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242599
  have eq243603 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq242660 eq1698
    | exact resolve eq1698 eq242660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698 eq242660
  have eq245332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243603 eq240622
    | exact resolve eq240622 eq243603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240622 eq243603
  have eq245446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq245332
  have eq245465 : x = (M.op x y) := by
    first
    | (have r₁ := eq245446
       have r₂ := eq28
       grind)
    | exact resolve eq245446 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245446
  have eq245471 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq245465 eq21
    | exact resolve eq21 eq245465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq245947 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq245471
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq245471
    | exact resolve eq245471 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245471
  have eq245963 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq245947 eq27
    | exact resolve eq27 eq245947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq247313 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq245963 eq204795
    | exact resolve eq204795 eq245963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204795
  have eq247470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq245947 eq247313
    | exact resolve eq247313 eq245947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247313
  have eq247496 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq247470
       have r₂ := eq28
       grind)
    | exact resolve eq247470 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247470
  have eq247508 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq245465 eq247496
    | exact resolve eq247496 eq245465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247496
  have eq253359 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq473 y
       have i₂ := eq247508
       grind)
    | exact superpose eq247508 eq473
    | exact resolve eq473 eq247508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq247508
  have eq253648 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq253359
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq253359
    | exact resolve eq253359 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253359
  have eq253722 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq245465 eq253648
    | exact resolve eq253648 eq245465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253648
  have eq253759 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq253722
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq253722
    | exact resolve eq253722 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253722
  have eq253775 : x = y ∨ x = y := by
    first
    | exact superpose eq245465 eq253759
    | exact resolve eq253759 eq245465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253759
  have eq253776 : x = y := by grind
  clear eq253775
  have eq253781 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq253776
       grind)
    | exact superpose eq253776 eq19
    | exact resolve eq19 eq253776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq253782 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq253776
       grind)
    | exact superpose eq253776 eq25
    | exact resolve eq25 eq253776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq253776
  have eq254091 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq253782
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq253782
    | exact resolve eq253782 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253782
  have eq254092 : x = (M.op x x) := by
    first
    | exact superpose eq245465 eq253781
    | exact resolve eq253781 eq245465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245465 eq253781
  have eq254223 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq245947 eq254091
    | exact resolve eq254091 eq245947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254091
  have eq254688 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq254223 eq245963
    | exact resolve eq245963 eq254223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245963 eq254223
  have eq255589 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq254092
       grind)
    | exact superpose eq254092 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq254092
       grind)
    | exact resolve eq13 eq254092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254092
  have eq255679 : x = (k x x) := by grind
  clear eq255589
  have eq256285 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq745 x x
       have i₂ := eq255679
       grind)
    | exact superpose eq255679 eq745
    | (have j0 := eq745 x x
       grind)
    | exact resolve eq745 eq255679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq255679
  have eq256288 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq256285
  have eq256289 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq256288
  have eq256301 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq256289
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq256289
    | exact resolve eq256289 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq256289
  have eq256327 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq245947 eq256301
    | exact resolve eq256301 eq245947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245947 eq256301
  have eq256351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq254688 eq256327
    | exact resolve eq256327 eq254688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254688 eq256327
  have eq256375 : False := by grind
  exact eq256375

/-- `Equation2656`: `x = ((x ◇ x) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyy_y_pxy_Equation2656 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2656 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2656.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq47 : (σ (k x (k x x))) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq36
    | exact resolve eq36 eq44
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) (M.op X2 X3)) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k (M.op (M.op X0 X0) (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X0) (M.op X1 X2)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X0) (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) (M.op X0 X2)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq97 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq108 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq168 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq264 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq287 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq420 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq287 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq287
    | exact resolve eq287 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq473 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
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
  have eq474 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X2 X2) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 X1 (M.op (M.op X0 X0) (M.op x x)) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op x x))
       have i₂ := eq53 X0 X1 x x
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq748 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1438 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) X0)
       have i₂ := eq541 X0 X0 X0
       grind)
    | exact superpose eq541 eq51
    | exact resolve eq51 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1439 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) X0)
       have i₂ := eq541 X0 X0 X0
       grind)
    | exact superpose eq541 eq52
    | exact resolve eq52 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1668 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq473 X0
       have i₂ := eq1438 X0
       grind)
    | exact superpose eq1438 eq473
    | exact resolve eq473 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1695 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x x) x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1438 eq474
    | exact resolve eq474 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1706 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq474 eq1695
    | exact resolve eq1695 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1740 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq51 eq1668
    | exact resolve eq1668 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1668
  have eq1874 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq617 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq473 X0
       grind)
    | exact superpose eq473 eq617
    | exact resolve eq617 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq617
  have eq1955 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1874 X0
       have i₂ := eq541 X0 X0 X0
       grind)
    | exact superpose eq541 eq1874
    | exact resolve eq1874 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq2011 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1439 eq474
    | exact resolve eq474 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq2024 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq474 eq2011
    | exact resolve eq2011 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq2011
  have eq2518 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq1955 (M.op (M.op X0 X0) X0)
       have i₂ := eq541 X0 X0 X0
       grind)
    | exact superpose eq541 eq1955
    | exact resolve eq1955 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq2526 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1955 X0
       have i₂ := eq1438 X0
       grind)
    | exact superpose eq1438 eq1955
    | exact resolve eq1955 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq2541 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2518 X0
       have i₂ := eq565 X0 X0
       grind)
    | exact superpose eq565 eq2518
    | exact resolve eq2518 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518
  have eq6150 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq168 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq168
    | (have j0 := eq168 x
       grind)
    | exact resolve eq168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq6176 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6150
  have eq6184 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6176
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq6176
    | exact resolve eq6176 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq6176
  have eq6192 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6184
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6184 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6184
  have eq6198 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6192 eq50
    | exact resolve eq50 eq6192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq8806 : (σ (k x (k x x))) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6192 eq47
    | exact resolve eq47 eq6192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq8807 : (σ (k x (k x x))) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq8806
       have i₂ := eq2541 sF2
       grind)
    | exact superpose eq2541 eq8806
    | exact resolve eq8806 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8806
  have eq8808 : (σ (k x (k x x))) = (M.op (M.op (σ x) (M.op x y)) x) := by
    first
    | (have i₁ := eq8807
       have i₂ := eq1438 sF2
       grind)
    | exact superpose eq1438 eq8807
    | exact resolve eq8807 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8807
  have eq17301 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6192 eq108
    | exact resolve eq108 eq6192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq6192
  have eq17375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17375
    | exact resolve eq17375 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17375
  have eq17383 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17376
       have r₂ := eq28
       grind)
    | exact resolve eq17376 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17376
  have eq17385 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17383
    | exact resolve eq17383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17383
  have eq17389 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq17385
  have eq17488 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17389
    | exact resolve eq17389 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17389
  have eq17489 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq17488
  have eq18089 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17489 eq58
    | exact resolve eq58 eq17489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq18090 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17489 eq113
    | exact resolve eq113 eq17489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq17489
  have eq18101 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18090
  have eq18106 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq18089
    | exact resolve eq18089 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18089
  have eq18110 : y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq18143 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2541 y
       have i₂ := eq18101
       grind)
    | exact superpose eq18101 eq2541
    | exact resolve eq2541 eq18101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18101
  have eq18196 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18143
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18143
    | exact resolve eq18143 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18143
  have eq18212 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18110
    | exact resolve eq18110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18110
  have eq18213 : y = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18212
  have eq18573 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq18196
       grind)
    | exact superpose eq18196 eq73
    | exact resolve eq73 eq18196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18196
  have eq18595 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18573
    | exact resolve eq18573 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18573
  have eq18774 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq748 x y
       have i₂ := eq18213
       grind)
    | exact superpose eq18213 eq748
    | (have j0 := eq748 x y
       grind)
    | exact resolve eq748 eq18213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18213
  have eq18777 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18774
  have eq18780 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18777
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18777
    | exact resolve eq18777 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18777
  have eq18791 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18780
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18780
    | exact resolve eq18780 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18780
  have eq18797 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18791
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18791
    | exact resolve eq18791 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18791
  have eq18801 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18797
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18797
    | exact resolve eq18797 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18797
  have eq18804 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18801
    | exact resolve eq18801 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18801
  have eq18805 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18804
  have eq18935 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18805 eq2541
    | exact resolve eq2541 eq18805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18805
  have eq18986 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq18935
    | exact resolve eq18935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18935
  have eq19231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18986 eq18595
    | exact resolve eq18595 eq18986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18595 eq18986
  have eq19237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19231
  have eq19239 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19237
       have r₂ := eq28
       grind)
    | exact resolve eq19237 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19237
  have eq19242 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ y)) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19239 eq52
    | exact resolve eq52 eq19239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq19271 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19239 eq2024
    | exact resolve eq2024 eq19239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19281 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq19271
    | exact resolve eq19271 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19271
  have eq19286 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19281 eq6198
    | exact resolve eq6198 eq19281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19322 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op x y)) x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19281 eq2526
    | exact resolve eq2526 eq19281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526
  have eq19382 : (M.op (M.op (σ x) (M.op x y)) x) = (σ (k x (τ (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8808
       have i₂ := eq19286
       grind)
    | exact superpose eq19286 eq8808
    | exact resolve eq8808 eq19286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8808
  have eq19420 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op x y)) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19382
       have i₂ := eq43 sF4
       grind)
    | exact superpose eq43 eq19382
    | exact resolve eq19382 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq19382
  have eq20411 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19281 eq19242
    | exact resolve eq19242 eq19281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19242 eq19281
  have eq20463 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq20411
  have eq20492 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19239 eq20463
    | exact resolve eq20463 eq19239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19239 eq20463
  have eq20532 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq20492
  have eq20553 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (M.op X0 X1))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq20532 eq53
    | exact resolve eq53 eq20532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq20532
  have eq20604 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20553 x x
       have i₂ := eq565 sF2 (M.op x x)
       grind)
    | exact superpose eq565 eq20553
    | exact resolve eq20553 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq20553
  have eq20619 : (τ (σ y)) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20604 eq6198
    | exact resolve eq6198 eq20604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6198
  have eq20648 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (M.op x y)) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20604 eq1438
    | exact resolve eq1438 eq20604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438 eq20604
  have eq20711 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq20619
    | exact resolve eq20619 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20619
  have eq20808 : y = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19286
       have i₂ := eq20711
       grind)
    | exact superpose eq20711 eq19286
    | exact resolve eq19286 eq20711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19286
  have eq20825 : y = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq20808
  have eq20977 : ∀ X0 : G, (k y (τ X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20825 eq420
    | exact resolve eq420 eq20825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq20825
  have eq20989 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (M.op (σ x) (σ y)) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20977 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq20977
    | exact resolve eq20977 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq20977
  have eq25004 : (σ x) = (k (M.op (σ x) (σ y)) (k (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19420 eq19322
    | exact resolve eq19322 eq19420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19322
  have eq25056 : (σ x) = (k (M.op (σ x) (σ y)) (k (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq25004
  have eq31672 : (M.op (σ y) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20648 eq19420
    | exact resolve eq19420 eq20648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19420 eq20648
  have eq31728 : (M.op (σ y) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq31672
  have eq35984 : (τ (σ x)) = (τ (k (σ y) (k (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25056 eq20989
    | exact resolve eq20989 eq25056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20989 eq25056
  have eq36056 : (τ (σ x)) = (τ (k (σ y) (k (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq35984
  have eq36111 : x = (τ (k (σ y) (k (σ x) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq36056
    | exact resolve eq36056 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36056
  have eq36351 : x = (τ (k (σ y) (M.op (σ y) (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31728 eq36111
    | exact resolve eq36111 eq31728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31728 eq36111
  have eq36413 : x = (τ (k (σ y) (M.op (σ y) (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq36351
  have eq52158 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18106
       grind)
    | exact superpose eq18106 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18106
  have eq52159 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq52158
  have eq52167 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52159
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52159
    | exact resolve eq52159 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52159
  have eq52168 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52167
  have eq52197 : y = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq52248 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2541 y
       have i₂ := eq52168
       grind)
    | exact superpose eq52168 eq2541
    | exact resolve eq2541 eq52168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52168
  have eq52317 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52248
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52248
    | exact resolve eq52248 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52248
  have eq52346 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52197
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52197
    | exact resolve eq52197 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52197
  have eq52347 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52346
  have eq52697 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq52317
       grind)
    | exact superpose eq52317 eq73
    | exact resolve eq73 eq52317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq52317
  have eq52723 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq52697
    | exact resolve eq52697 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52697
  have eq52942 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq748 x y
       have i₂ := eq52347
       grind)
    | exact superpose eq52347 eq748
    | (have j0 := eq748 x y
       grind)
    | exact resolve eq748 eq52347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52347
  have eq52945 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52942
  have eq52952 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52945
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52945
    | exact resolve eq52945 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52945
  have eq52965 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52952
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52952
    | exact resolve eq52952 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52952
  have eq52971 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52965
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52965
    | exact resolve eq52965 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52965
  have eq52975 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52971
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52971
    | exact resolve eq52971 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52971
  have eq52978 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq52975
    | exact resolve eq52975 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52975
  have eq52979 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq52978
  have eq55233 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52979 eq2541
    | exact resolve eq2541 eq52979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541 eq52979
  have eq55343 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq55233
    | exact resolve eq55233 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55233
  have eq56079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55343 eq52723
    | exact resolve eq52723 eq55343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52723 eq55343
  have eq56085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq56079
  have eq56089 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq56085
       have r₂ := eq28
       grind)
    | exact resolve eq56085 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56085
  have eq56192 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56089 eq28
    | exact resolve eq28 eq56089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56231 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56089 eq2024
    | exact resolve eq2024 eq56089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq56500 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq56231
    | exact resolve eq56231 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56231
  have eq56646 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq56500
  have eq206936 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56089 eq56646
    | exact resolve eq56646 eq56089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56089 eq56646
  have eq206977 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq206936
  have eq208843 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206977 eq80
    | exact resolve eq80 eq206977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206977
  have eq208883 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq208843
    | exact resolve eq208843 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq208843
  have eq215396 : x = (τ (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq208883 eq36413
    | exact resolve eq36413 eq208883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36413 eq208883
  have eq215598 : x = (τ (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq215396
  have eq215702 : x = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq215598
       have r₂ := eq56192
       grind)
    | exact resolve eq215598 eq56192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215598
  have eq215751 : x = (k y x) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq80 eq215702
    | exact resolve eq215702 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq215702
  have eq215752 : x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq215751
  have eq218094 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq215752
       grind)
    | exact superpose eq215752 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq215752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218095 : y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq218094
  have eq242977 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1740 x
       have i₂ := eq218095
       grind)
    | exact superpose eq218095 eq1740
    | exact resolve eq1740 eq218095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218095
  have eq243152 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq242977
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq242977
    | exact resolve eq242977 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242977
  have eq243153 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq243152
  have eq243179 : x ≠ x ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq243153
       grind)
    | exact superpose eq243153 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq243153
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq243153
       grind)
    | exact resolve eq13 eq243153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243182 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq243153
       grind)
    | exact superpose eq243153 eq54
    | exact resolve eq54 eq243153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq243153
  have eq243273 : (k y x) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq243179
  have eq243323 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq243182
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq243182
    | exact resolve eq243182 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243182
  have eq243649 : x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq215752
       have i₂ := eq243273
       grind)
    | exact superpose eq243273 eq215752
    | exact resolve eq215752 eq243273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215752 eq243273
  have eq243662 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq243649
  have eq243696 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq243323
       have i₂ := eq243662
       grind)
    | exact superpose eq243662 eq243323
    | exact resolve eq243323 eq243662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243323
  have eq243786 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq243662
       grind)
    | exact superpose eq243662 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq243662
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq243662
       grind)
    | exact resolve eq13 eq243662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243662
  have eq243878 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq243786
  have eq243881 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq243696
  have eq243949 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243881 eq21
    | exact resolve eq21 eq243881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244043 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq243881 eq1706
    | exact resolve eq1706 eq243881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706 eq243881
  have eq244268 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq244043
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq244043
    | exact resolve eq244043 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244043
  have eq244323 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq243949
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq243949
    | exact resolve eq243949 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243949
  have eq244333 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq244323 eq27
    | exact resolve eq27 eq244323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244323
  have eq244714 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20711
       have i₂ := eq243878
       grind)
    | exact superpose eq243878 eq20711
    | exact resolve eq20711 eq243878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20711 eq243878
  have eq244751 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq244714
  have eq244774 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq244751
       have r₂ := eq56192
       grind)
    | exact resolve eq244751 eq56192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56192 eq244751
  have eq250987 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17301
       have i₂ := eq244268
       grind)
    | exact superpose eq244268 eq17301
    | exact resolve eq17301 eq244268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17301 eq244268
  have eq251176 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq250987
  have eq251240 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq251176
    | exact resolve eq251176 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251176
  have eq253937 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq251240 eq1740
    | exact resolve eq1740 eq251240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740 eq251240
  have eq256849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq253937 eq244333
    | exact resolve eq244333 eq253937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244333 eq253937
  have eq256968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq256849
  have eq256990 : x = (M.op x y) := by
    first
    | (have r₁ := eq256968
       have r₂ := eq28
       grind)
    | exact resolve eq256968 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256968
  have eq257000 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq256990 eq21
    | exact resolve eq21 eq256990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq257342 : x = y ∨ x = y := by
    first
    | exact superpose eq256990 eq244774
    | exact resolve eq244774 eq256990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244774
  have eq257343 : x = y := by grind
  clear eq257342
  have eq257478 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq257000
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq257000
    | exact resolve eq257000 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257000
  have eq257493 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq257343
       grind)
    | exact superpose eq257343 eq19
    | exact resolve eq19 eq257343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq257494 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq257343
       grind)
    | exact superpose eq257343 eq25
    | exact resolve eq25 eq257343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq257343
  have eq257806 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq257494
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq257494
    | exact resolve eq257494 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257494
  have eq257807 : x = (M.op x x) := by
    first
    | exact superpose eq256990 eq257493
    | exact resolve eq257493 eq256990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256990 eq257493
  have eq257827 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq257478 eq27
    | exact resolve eq27 eq257478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq259208 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq257478 eq257806
    | exact resolve eq257806 eq257478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257806
  have eq260377 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq257807
       grind)
    | exact superpose eq257807 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq257807
       grind)
    | exact resolve eq13 eq257807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257807
  have eq260471 : x = (k x x) := by grind
  clear eq260377
  have eq260634 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq259208 eq257827
    | exact resolve eq257827 eq259208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257827 eq259208
  have eq261083 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq748 x x
       have i₂ := eq260471
       grind)
    | exact superpose eq260471 eq748
    | (have j0 := eq748 x x
       grind)
    | exact resolve eq748 eq260471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748 eq260471
  have eq261086 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq261083
  have eq261087 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq261086
  have eq261097 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq261087
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq261087
    | exact resolve eq261087 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq261087
  have eq261121 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq257478 eq261097
    | exact resolve eq261097 eq257478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257478 eq261097
  have eq261145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq260634 eq261121
    | exact resolve eq261121 eq260634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260634 eq261121
  have eq261169 : False := by grind
  exact eq261169

/-- `Equation2663`: `x = ((x ◇ y) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pxy_pxy_x_pxy_Equation2663 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2663 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2663.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = X0 := by
    intro X0 X1
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
  have eq50 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq43
    | exact resolve eq43 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq66 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq62 sF2
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq75 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y x) ∨ x = (k x y) := by
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
  have eq76 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq112 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq822
    | exact resolve eq822 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq826 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq823
       have r₂ := eq27
       grind)
    | exact resolve eq823 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq828 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq826
    | exact resolve eq826 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq830 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq828 eq76
    | (have r₁ := eq76
       have r₂ := eq828
       grind)
    | exact resolve eq76 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq841 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq830
  have eq2079 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq841 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq2081 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2079
       have r₂ := eq828
       grind)
    | exact resolve eq2079 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq2079
  have eq2082 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq2081
    | exact resolve eq2081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq3062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq112 eq2082
    | exact resolve eq2082 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2082 eq112
    | exact resolve eq112 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq2082
  have eq3068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq3064
  have eq3069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq3062
  have eq3070 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq3068
       have r₂ := eq27
       grind)
    | exact resolve eq3068 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3068
  have eq3071 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3069
       have r₂ := eq27
       grind)
    | exact resolve eq3069 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069
  have eq3075 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq3071
       grind)
    | exact superpose eq3071 eq66
    | exact resolve eq66 eq3071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3071
  have eq3091 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq3075
    | exact resolve eq3075 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq3193 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq3070 eq58
    | exact resolve eq58 eq3070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq3070
  have eq3199 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq3193
    | exact resolve eq3193 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3193
  have eq3643 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq3199
       grind)
    | exact superpose eq3199 eq75
    | (have r₁ := eq75
       have r₂ := eq3199
       grind)
    | exact resolve eq75 eq3199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq3645 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq3199
       grind)
    | exact superpose eq3199 eq66
    | exact resolve eq66 eq3199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3661 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq3643
  have eq3662 : (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq3661
  have eq3664 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq3645
    | exact resolve eq3645 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3645
  have eq4111 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq3662
       grind)
    | exact superpose eq3662 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq4117 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq4111
       have r₂ := eq3199
       grind)
    | exact resolve eq4111 eq3199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3199 eq4111
  have eq4118 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4117
    | exact resolve eq4117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4117
  have eq4349 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq4118
       grind)
    | exact superpose eq4118 eq44
    | exact resolve eq44 eq4118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118
  have eq4352 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq4349
    | exact resolve eq4349 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4349
  have eq4368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq4352 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq4352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4352
  have eq4369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq4368
    | exact resolve eq4368 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4368
  have eq4372 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq4369
       have r₂ := eq27
       grind)
    | exact resolve eq4369 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4369
  have eq4374 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq4372
    | exact resolve eq4372 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4372
  have eq4390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4374 eq3664
    | exact resolve eq3664 eq4374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3664 eq4374
  have eq4406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq4390
  have eq4410 : x = (k x y) := by
    first
    | (have r₁ := eq4406
       have r₂ := eq27
       grind)
    | exact resolve eq4406 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4406
  have eq4417 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq4410
       grind)
    | exact superpose eq4410 eq44
    | exact resolve eq44 eq4410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq4418 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq84 x y
       have i₂ := eq4410
       grind)
    | exact superpose eq4410 eq84
    | (have j0 := eq84 x y
       grind)
    | exact resolve eq84 eq4410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4410
  have eq4419 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4418
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4418
    | exact resolve eq4418 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4418
  have eq4420 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4417
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4417
    | exact resolve eq4417 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4417
  have eq4422 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4419
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4419
    | exact resolve eq4419 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4419
  have eq4431 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4420 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq4420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq4420
  have eq4432 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4431
    | exact resolve eq4431 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4431
  have eq4435 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4432
    | exact resolve eq4432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4432
  have eq4440 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq4422
       grind)
    | exact superpose eq4422 eq66
    | exact resolve eq66 eq4422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4422
  have eq4459 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4440
    | exact resolve eq4440 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4440
  have eq4473 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4435 eq3091
    | exact resolve eq3091 eq4435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4493 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4473
       have r₂ := eq27
       grind)
    | exact resolve eq4473 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4473
  have eq4496 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4493 eq51
    | exact resolve eq51 eq4493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4558 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq54 eq4496
    | exact resolve eq4496 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq4496
  have eq4590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4459 eq4435
    | exact resolve eq4435 eq4459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4607 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4590
       have r₂ := eq27
       grind)
    | exact resolve eq4590 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4590
  have eq4610 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4607 eq27
    | exact resolve eq27 eq4607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4607
  have eq4937 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4493 eq4558
    | exact resolve eq4558 eq4493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4493 eq4558
  have eq4971 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4937
  have eq5389 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4971 eq3091
    | exact resolve eq3091 eq4971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091
  have eq5394 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4971 eq4459
    | exact resolve eq4459 eq4971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459 eq4971
  have eq5410 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5394
  have eq5414 : (σ (M.op x y)) = (σ x) := by grind
  clear eq5389
  have eq5422 : x = (M.op x y) := by
    first
    | (have r₁ := eq5410
       have r₂ := eq4610
       grind)
    | exact resolve eq5410 eq4610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610 eq5410
  have eq5649 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5414 eq4435
    | exact resolve eq4435 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4435
  have eq5656 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq5649
       have r₂ := eq27
       grind)
    | exact resolve eq5649 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5649
  have eq5670 : x = (M.op (M.op x x) y) := by
    first
    | exact superpose eq5422 eq50
    | exact resolve eq50 eq5422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5706 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5670
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq5670
    | exact resolve eq5670 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq5670
  have eq5711 : x = (M.op x x) := by
    first
    | exact superpose eq5422 eq5706
    | exact resolve eq5706 eq5422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5422 eq5706
  have eq6538 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq5711
       grind)
    | exact superpose eq5711 eq66
    | exact resolve eq66 eq5711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq5711
  have eq6564 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5414 eq6538
    | exact resolve eq6538 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6538
  have eq6568 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5656 eq6564
    | exact resolve eq6564 eq5656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656 eq6564
  have eq6570 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6568
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6568
    | exact resolve eq6568 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6568
  have eq6572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5414 eq6570
    | exact resolve eq6570 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414 eq6570
  have eq6573 : False := by grind
  exact eq6573
