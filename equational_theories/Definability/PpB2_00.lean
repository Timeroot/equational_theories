import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_y_pxy_x_pxy_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
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
  have eq85 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq94 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq92
    | exact resolve eq92 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq94
    | exact resolve eq94 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq44
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq44 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq124
    | exact resolve eq124 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq148 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq151 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq148
    | exact resolve eq148 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq153 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq151
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq151
    | exact resolve eq151 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq151
  have eq255 : ∀ X1 : G, (M.op y (M.op X1 (M.op (M.op y (M.op x y)) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq56 X0 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq127 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq127
  have eq831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq830
    | exact resolve eq830 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq834 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq831
       have r₂ := eq27
       grind)
    | exact resolve eq831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq839 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq834 eq56
    | exact resolve eq56 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq839 eq834
    | exact resolve eq834 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq839
  have eq939 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq929
  have eq941 : (τ (σ y)) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq939 eq71
    | exact resolve eq71 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq939
  have eq954 : y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq941
    | exact resolve eq941 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq941
  have eq978 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq954
       grind)
    | exact superpose eq954 eq50
    | exact resolve eq50 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq992 : y = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq978
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq978
    | exact resolve eq978 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1002 : y = (M.op y x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq56
    | exact resolve eq56 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1022 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq1002
       grind)
    | exact superpose eq1002 eq50
    | exact resolve eq50 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1036 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1022
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1022
    | exact resolve eq1022 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1022
  have eq1037 : x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq1036
  have eq1038 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1037 eq153
    | exact resolve eq153 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq1041 : ∀ X0 : G, (M.op x (M.op X0 (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1037 eq14
    | exact resolve eq14 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1037 eq14
    | exact resolve eq14 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1046 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1037 eq56
    | exact resolve eq56 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1048 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1038
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1038
    | exact resolve eq1038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1038
  have eq1051 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1046 eq14
    | exact resolve eq14 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1077 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1048 eq14
    | exact resolve eq14 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1078 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ (M.op x y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1048 eq14
    | exact resolve eq14 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1098 : (M.op x y) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1037 eq1041
    | exact resolve eq1041 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1378 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq53 eq270
    | exact resolve eq270 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1381 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq1078 eq270
    | exact resolve eq270 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1431 : (M.op x y) = (M.op y (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1037 eq1378
    | exact resolve eq1378 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1450 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op (M.op x y) x) (M.op x y))) := by
    first
    | exact superpose eq1431 eq50
    | exact resolve eq50 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1709 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq1450 eq14
    | exact resolve eq14 eq1450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1712 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op x y) x)) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op x y) x)) (M.op (M.op (M.op x y) x) (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1450 eq55
    | exact resolve eq55 eq1450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1717 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op x y) (M.op (M.op (M.op x y) x) (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1042 eq1712
    | exact resolve eq1712 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq1719 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1042 eq1709
    | exact resolve eq1709 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq1709
  have eq1724 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq1450 eq1717
    | exact resolve eq1717 eq1450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450 eq1717
  have eq1725 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq1719 x
       have i₂ := eq56 sF0 x
       grind)
    | exact superpose eq56 eq1719
    | exact resolve eq1719 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1727 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq1037 eq1725
    | exact resolve eq1725 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq1725
  have eq1817 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) x) (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)))) := by
    intro X0
    first
    | exact superpose eq1724 eq270
    | exact resolve eq270 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq1818 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op x y) x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1051 eq1817
    | exact resolve eq1817 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq1817
  have eq1825 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq1727 eq1818
    | exact resolve eq1818 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq1880 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1727 eq1825
    | exact resolve eq1825 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1883 : x = (M.op y (M.op x (M.op (M.op x y) x))) := by
    first
    | exact superpose eq1825 eq255
    | exact resolve eq255 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq1825
  have eq1897 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1098 eq1883
    | exact resolve eq1883 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq1883
  have eq1900 : ∀ X0 : G, y = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq1897 eq53
    | exact resolve eq53 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1897
  have eq1918 : y = (M.op x x) := by
    first
    | (have i₁ := eq1900 x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq1900
    | exact resolve eq1900 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1921 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1918
       grind)
    | exact superpose eq1918 eq72
    | exact resolve eq72 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1941 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1921
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1921
    | exact resolve eq1921 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1921
  have eq2022 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1941 eq1381
    | exact resolve eq1381 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq2026 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1941 eq54
    | exact resolve eq54 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq2031 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1941 eq14
    | exact resolve eq14 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2035 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1941 eq56
    | exact resolve eq56 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2041 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq2031
    | (have j0 := eq2031 X0
       grind)
    | exact resolve eq2031 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2044 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2022
    | exact resolve eq2022 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq2108 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2035 eq51
    | exact resolve eq51 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2035
  have eq2127 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2108
    | exact resolve eq2108 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2108
  have eq2216 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq2044 eq1077
    | exact resolve eq1077 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077 eq2044
  have eq2230 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1880
       have i₂ := eq1918
       grind)
    | exact superpose eq1918 eq1880
    | exact resolve eq1880 eq1918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880 eq1918
  have eq2296 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2230 eq1431
    | exact resolve eq1431 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431 eq2230
  have eq2326 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq2296
       grind)
    | exact superpose eq2296 eq96
    | exact resolve eq96 eq2296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2296
  have eq2346 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq2326
    | exact resolve eq2326 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2326
  have eq2748 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2026 eq270
    | exact resolve eq270 eq2026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq2026
  have eq2763 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq2127 eq2748
    | exact resolve eq2748 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127 eq2748
  have eq3183 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2216 eq14
    | exact resolve eq14 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq3194 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2041 eq3183
    | exact resolve eq3183 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041 eq3183
  have eq3199 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3194 x
       have i₂ := eq56 sF2 x
       grind)
    | exact superpose eq56 eq3194
    | exact resolve eq3194 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq3194
  have eq3201 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1941 eq3199
    | exact resolve eq3199 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941 eq3199
  have eq3204 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3201 eq2763
    | exact resolve eq2763 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763 eq3201
  have eq3224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2346 eq3204
    | exact resolve eq3204 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346 eq3204
  have eq3230 : False := by grind
  exact eq3230

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pxx_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (k (M.op X1 X2) (M.op X0 (M.op X2 X0))) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X1 X2) (M.op X0 (M.op X2 X0))
       grind)
    | (have r₁ := eq13 (M.op X1 X2) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq98 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq105
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq214 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq50 (M.op y y)
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq51 (M.op sF3 sF3)
       have i₂ := eq14 sF3 sF3 sF3
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) X0
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq56 X0 X0
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq56 X0 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq441 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq341 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq341
    | exact resolve eq341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq341 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq341
    | (have j0 := eq341 X0 x
       grind)
    | exact resolve eq341 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq511 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X1 X2
       have i₂ := eq52 X2 X3 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq52 y X1 X0
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq52 sF3 x x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op (M.op y (M.op x y)) y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 x (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq56 (M.op (M.op X0 (M.op X0 X0)) X0) x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq768 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq68 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq851 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq863 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq851 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq851 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq851 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq851 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq873 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq863 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq863
    | (have j0 := eq863 X0 X1
       grind)
    | exact resolve eq863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1319 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq252 X0 x x
       grind)
    | exact superpose eq252 eq56
    | exact resolve eq56 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1323 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1319 X0
       have i₂ := eq252 X0 X0 X0
       grind)
    | exact superpose eq252 eq1319
    | exact resolve eq1319 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq3730 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq697 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1323 sF0
       grind)
    | exact superpose eq1323 eq697
    | exact resolve eq697 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3755 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3730
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3730
    | exact resolve eq3730 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730
  have eq3757 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3755 eq697
    | exact resolve eq697 eq3755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq3755
  have eq3782 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3757 eq14
    | exact resolve eq14 eq3757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3814 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq698 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1323 sF4
       grind)
    | exact superpose eq1323 eq698
    | exact resolve eq698 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3839 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3814
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3814
    | exact resolve eq3814 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq3859 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3839 eq698
    | exact resolve eq698 eq3839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3839
  have eq3884 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3859 eq14
    | exact resolve eq14 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3949 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3782 eq50
    | exact resolve eq50 eq3782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq3972 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq3949 eq3757
    | exact resolve eq3757 eq3949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3757
  have eq4125 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3884 eq51
    | exact resolve eq51 eq3884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3884
  have eq4148 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4125 eq3859
    | exact resolve eq3859 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859
  have eq5599 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq511 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq252 X0 x X2
       grind)
    | exact superpose eq252 eq511
    | exact resolve eq511 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq5693 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq5599 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq5599
    | exact resolve eq5599 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5599
  have eq5703 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5693 X0 x
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq5693
    | exact resolve eq5693 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5693
  have eq6515 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq711 X0 X1 X2 X3
       have i₂ := eq5703 X0
       grind)
    | exact superpose eq5703 eq711
    | exact resolve eq711 eq5703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq6526 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6515 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq252 X0 x x
       grind)
    | exact superpose eq252 eq6515
    | exact resolve eq6515 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6515
  have eq6739 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6526 X0 X1 X2
       have i₂ := eq252 X0 X0 X0
       grind)
    | exact superpose eq252 eq6526
    | exact resolve eq6526 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq6774 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6739 X0 X1 X2
       have i₂ := eq5703 X0
       grind)
    | exact superpose eq5703 eq6739
    | exact resolve eq6739 eq5703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703 eq6739
  have eq6831 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq6774 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6774
    | (have j0 := eq6774 y X0 x
       grind)
    | exact resolve eq6774 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6843 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq6774
    | (have j0 := eq6774 (σ y) X0 (σ x)
       grind)
    | exact resolve eq6774 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6919 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq698 X0
       have i₂ := eq6774 X0 X0 sF4
       grind)
    | exact superpose eq6774 eq698
    | exact resolve eq698 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq7135 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq724 X0
       have i₂ := eq6774 X0 X0 X0
       grind)
    | exact superpose eq6774 eq724
    | exact resolve eq724 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq7177 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq251 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq7135 X0
       grind)
    | exact superpose eq7135 eq251
    | (have j0 := eq251 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq251 (M.op X0 X0) X0
       have r₂ := eq7135 X0
       grind)
    | exact resolve eq251 eq7135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq7184 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7177
  have eq7189 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq7184 X0
       have i₂ := eq252 X0 X0 X0
       grind)
    | exact superpose eq252 eq7184
    | exact resolve eq7184 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7184
  have eq7518 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq768 X0 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq768
    | exact resolve eq768 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq7526 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq7518 X0
       have i₂ := eq7135 X0
       grind)
    | exact superpose eq7135 eq7518
    | exact resolve eq7518 eq7135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7135 eq7518
  have eq7939 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq98 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq98
    | (have j0 := eq98 y
       grind)
    | exact resolve eq98 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq7966 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq7939
  have eq7975 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7966
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq7966
    | exact resolve eq7966 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq7966
  have eq8000 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq7975
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq7975 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7975
  have eq8023 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq8000 eq90
    | exact resolve eq90 eq8000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq10307 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X1
       have i₂ := eq6774 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq6774 eq520
    | exact resolve eq520 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq10429 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq10307 X0 x
       grind)
    | exact superpose eq10307 eq52
    | exact resolve eq52 eq10307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10307
  have eq10572 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq10429 (M.op X0 (M.op X0 X0))
       have i₂ := eq252 X0 X0 X0
       grind)
    | exact superpose eq252 eq10429
    | exact resolve eq10429 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10429
  have eq10696 : ∀ X0 : G, (k (M.op y (M.op (M.op x y) X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq7189 X0
       have i₂ := eq10572 X0
       grind)
    | exact superpose eq10572 eq7189
    | exact resolve eq7189 eq10572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7189
  have eq10699 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1323 X0
       have i₂ := eq10572 X0
       grind)
    | exact superpose eq10572 eq1323
    | exact resolve eq1323 eq10572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq10720 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq6919 sF4
       have i₂ := eq10572 sF4
       grind)
    | exact superpose eq10572 eq6919
    | exact resolve eq6919 eq10572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6919
  have eq10791 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq10572 eq14
    | exact resolve eq14 eq10572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10818 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10791 X0 X1
       have i₂ := eq14 X0 sF0 X0
       grind)
    | exact superpose eq14 eq10791
    | exact resolve eq10791 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10791
  have eq10853 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4125 eq10720
    | exact resolve eq10720 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10720
  have eq10932 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq521 X0 X1
       have i₂ := eq6774 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq6774 eq521
    | exact resolve eq521 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq11209 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq10932 eq52
    | exact resolve eq52 eq10932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10932
  have eq11366 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq11209 (M.op X0 (M.op X0 X0))
       have i₂ := eq252 X0 X0 X0
       grind)
    | exact superpose eq252 eq11209
    | exact resolve eq11209 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq11209
  have eq11682 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op x y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq709 X0 X1 X2
       have i₂ := eq10818 (M.op y sF0) (M.op y sF0)
       grind)
    | exact superpose eq10818 eq709
    | exact resolve eq709 eq10818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq10818
  have eq11683 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3972 eq11682
    | exact resolve eq11682 eq3972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3972 eq11682
  have eq11684 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6831 eq11683
    | exact resolve eq11683 eq6831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6831 eq11683
  have eq11790 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq11366 eq14
    | exact resolve eq14 eq11366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11366
  have eq11817 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11790 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq11790
    | exact resolve eq11790 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11790
  have eq12343 : (M.op y y) = (M.op x (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq11684 (M.op x (M.op x x)) x x
       have i₂ := eq52 x x x
       grind)
    | exact superpose eq52 eq11684
    | exact resolve eq11684 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11684
  have eq12480 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq11817 eq710
    | exact resolve eq710 eq11817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq11817
  have eq12481 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4148 eq12480
    | exact resolve eq12480 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148 eq12480
  have eq12482 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6843 eq12481
    | exact resolve eq12481 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6843 eq12481
  have eq12511 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq12482 (M.op x (M.op x x)) x sF2
       have i₂ := eq52 x x sF2
       grind)
    | exact superpose eq52 eq12482
    | exact resolve eq12482 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12482
  have eq13856 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq518 X0 X1 X2 X3
       have i₂ := eq6774 X0 X0 (M.op X2 (M.op X3 X2))
       grind)
    | exact superpose eq6774 eq518
    | exact resolve eq518 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq6774
  have eq14107 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 x X2
       have i₂ := eq13856 X2 X0 X1 x
       grind)
    | exact superpose eq13856 eq52
    | exact resolve eq52 eq13856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq13856
  have eq14700 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op (M.op X1 X0) (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq3949 eq14107
    | exact resolve eq14107 eq3949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14107
  have eq15967 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10853 eq12511
    | exact resolve eq12511 eq10853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10853 eq12511
  have eq31012 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8000 eq112
    | exact resolve eq112 eq8000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq8000
  have eq31028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq31028
    | exact resolve eq31028 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31028
  have eq31047 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq31036
       have r₂ := eq27
       grind)
    | exact resolve eq31036 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31036
  have eq31049 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq31047
    | exact resolve eq31047 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31047
  have eq31053 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31049 eq51
    | exact resolve eq51 eq31049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31049
  have eq31130 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq31053
    | exact resolve eq31053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31053
  have eq31143 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4125 eq31130
    | exact resolve eq31130 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31130
  have eq31179 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq31143 eq54
    | exact resolve eq54 eq31143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31143
  have eq31281 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq31179 x
       have i₂ := eq56 sF2 x
       grind)
    | exact superpose eq56 eq31179
    | exact resolve eq31179 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31179
  have eq36977 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31281 eq7526
    | exact resolve eq7526 eq31281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31281
  have eq37066 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq36977
    | exact resolve eq36977 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36977
  have eq38606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq37066 eq118
    | exact resolve eq118 eq37066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq37066
  have eq38624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq38606
  have eq38626 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq38624
       have r₂ := eq27
       grind)
    | exact resolve eq38624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38624
  have eq38630 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq38626
       grind)
    | exact superpose eq38626 eq50
    | exact resolve eq50 eq38626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq38626
  have eq38706 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38630
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38630
    | exact resolve eq38630 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38630
  have eq38718 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3949 eq38706
    | exact resolve eq38706 eq3949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3949 eq38706
  have eq38832 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq38718 eq53
    | exact resolve eq53 eq38718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq38718
  have eq38934 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38832 x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq38832
    | exact resolve eq38832 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38832
  have eq38957 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7526 x
       have i₂ := eq38934
       grind)
    | exact superpose eq38934 eq7526
    | exact resolve eq7526 eq38934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38934
  have eq39049 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38957
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38957
    | exact resolve eq38957 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38957
  have eq39167 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq39049
       grind)
    | exact superpose eq39049 eq75
    | exact resolve eq75 eq39049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq39049
  have eq39201 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq39167
    | exact resolve eq39167 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39167
  have eq39547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39201 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq39201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq39547
    | exact resolve eq39547 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39547
  have eq39571 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq39560
       have r₂ := eq27
       grind)
    | exact resolve eq39560 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39560
  have eq39573 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq39571
    | exact resolve eq39571 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39571
  have eq39574 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39573
  have eq40436 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39574 eq51
    | exact resolve eq51 eq39574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq39574
  have eq40518 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq40436
    | exact resolve eq40436 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40436
  have eq40533 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4125 eq40518
    | exact resolve eq40518 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4125 eq40518
  have eq40669 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40533 eq54
    | exact resolve eq54 eq40533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq40533
  have eq40776 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40669 x
       have i₂ := eq56 sF2 x
       grind)
    | exact superpose eq56 eq40669
    | exact resolve eq40669 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40669
  have eq41734 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40776 eq7526
    | exact resolve eq7526 eq40776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7526 eq40776
  have eq41832 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq41734
    | exact resolve eq41734 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41734
  have eq41988 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41832 eq39201
    | exact resolve eq39201 eq41832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39201 eq41832
  have eq42000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41988
  have eq42004 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq42000
       have r₂ := eq27
       grind)
    | exact resolve eq42000 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42000
  have eq42012 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42004 eq79
    | (have r₁ := eq79
       have r₂ := eq42004
       grind)
    | exact resolve eq79 eq42004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq42013 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42004 eq223
    | exact resolve eq223 eq42004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq42064 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42004 eq15967
    | exact resolve eq15967 eq42004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15967 eq42004
  have eq42072 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq42012
  have eq42074 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10699 eq42064
    | exact resolve eq42064 eq10699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10699 eq42064
  have eq42088 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq42013
    | exact resolve eq42013 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42013
  have eq43120 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42074 eq8023
    | exact resolve eq8023 eq42074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43152 : (M.op (σ y) (σ x)) = (M.op y (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42074 eq10572
    | exact resolve eq10572 eq42074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10572 eq42074
  have eq43237 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq43120
    | exact resolve eq43120 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq43120
  have eq43247 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42088 eq8023
    | exact resolve eq8023 eq42088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43278 : (σ y) = (k (M.op y (M.op (M.op x y) (σ y))) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42088 eq10696
    | exact resolve eq10696 eq42088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10696
  have eq44286 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq43237
       grind)
    | exact superpose eq43237 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq43237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44307 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq44286
  have eq44376 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43237
       have i₂ := eq43247
       grind)
    | exact superpose eq43247 eq43237
    | exact resolve eq43237 eq43247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43247
  have eq44401 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq44376
  have eq44486 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq44401 eq441
    | exact resolve eq441 eq44401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq44401
  have eq44493 : ∀ X0 : G, (τ (k X0 (σ x))) = (τ (k X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq44486 X0
       have i₂ := eq456 X0
       grind)
    | exact superpose eq456 eq44486
    | exact resolve eq44486 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq44486
  have eq57692 : (σ y) = (k (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43152 eq43278
    | exact resolve eq43278 eq43152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43152 eq43278
  have eq57708 : (σ y) = (k (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq57692
  have eq74670 : (τ (σ y)) = (τ (k (M.op (σ y) (σ x)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57708 eq44493
    | exact resolve eq44493 eq57708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44493 eq57708
  have eq74749 : (τ (σ y)) = (τ (k (M.op (σ y) (σ x)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq74670
  have eq74798 : y = (τ (k (M.op (σ y) (σ x)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq74749
    | exact resolve eq74749 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74749
  have eq121415 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42072 eq85
    | exact resolve eq85 eq42072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42072
  have eq121460 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq121415
    | exact resolve eq121415 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq121415
  have eq123953 : y = (τ (k (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121460 eq74798
    | exact resolve eq74798 eq121460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74798 eq121460
  have eq124059 : y = (τ (k (σ y) (σ x))) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq123953
  have eq124145 : y = (k y x) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq85 eq124059
    | exact resolve eq124059 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq124059
  have eq124146 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq124145
  have eq124209 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq124146
       grind)
    | exact superpose eq124146 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq124146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124146
  have eq124230 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124209
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124209
    | exact resolve eq124209 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124209
  have eq124250 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124230
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124230
    | exact resolve eq124230 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124230
  have eq124251 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq124250
  have eq125898 : (M.op x y) = (M.op x (M.op y (M.op y (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14700 x y
       have i₂ := eq124251
       grind)
    | exact superpose eq124251 eq14700
    | exact resolve eq14700 eq124251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14700 eq124251
  have eq125945 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12343 eq125898
    | exact resolve eq125898 eq12343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12343 eq125898
  have eq126150 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31012
       have i₂ := eq125945
       grind)
    | exact superpose eq125945 eq31012
    | exact resolve eq31012 eq125945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125945
  have eq126281 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq126150
  have eq126332 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq126281
    | exact resolve eq126281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126281
  have eq127991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126332 eq42088
    | exact resolve eq42088 eq126332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42088 eq126332
  have eq128166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq127991
  have eq128212 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq128166
       have r₂ := eq27
       grind)
    | exact resolve eq128166 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128166
  have eq128439 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq128212
  have eq2181659 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq44307
       grind)
    | exact superpose eq44307 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq44307
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq44307
       grind)
    | exact resolve eq13 eq44307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44307
  have eq2181866 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq2181659
  have eq2223500 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43237
       have i₂ := eq2181866
       grind)
    | exact superpose eq2181866 eq43237
    | exact resolve eq43237 eq2181866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43237 eq2181866
  have eq2223650 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq2223500
  have eq2223721 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2223650
       have r₂ := eq128439
       grind)
    | exact resolve eq2223650 eq128439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128439 eq2223650
  have eq2224217 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq2223721
       grind)
    | exact superpose eq2223721 eq56
    | exact resolve eq56 eq2223721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223721
  have eq2224548 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2224217
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2224217
    | exact resolve eq2224217 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224217
  have eq2224549 : x = (M.op x y) := by grind
  clear eq2224548
  have eq2224760 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2224549 eq20
    | exact resolve eq20 eq2224549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2224811 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2224549 eq214
    | exact resolve eq214 eq2224549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq2225374 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2224811
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2224811
    | exact resolve eq2224811 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2224811
  have eq2225419 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2224760
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2224760
    | exact resolve eq2224760 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224760
  have eq2225438 : x = (M.op y y) := by
    first
    | exact superpose eq2224549 eq2225374
    | exact resolve eq2225374 eq2224549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225374
  have eq2225515 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2225419 eq26
    | exact resolve eq26 eq2225419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2227213 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq31012
       have i₂ := eq2225438
       grind)
    | exact superpose eq2225438 eq31012
    | exact resolve eq31012 eq2225438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31012
  have eq2227531 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2225438
       grind)
    | exact superpose eq2225438 eq13
    | exact resolve eq13 eq2225438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225438
  have eq2228045 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2227213
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2227213
    | exact resolve eq2227213 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227213
  have eq2228207 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2225419 eq2228045
    | exact resolve eq2228045 eq2225419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228045
  have eq2306100 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq2228207 eq8023
    | exact resolve eq8023 eq2228207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8023
  have eq2306523 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2228207 eq56
    | exact resolve eq56 eq2228207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2228207
  have eq2306875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2225515 eq2306523
    | exact resolve eq2306523 eq2225515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306523
  have eq2307075 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq2306100
    | exact resolve eq2306100 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2306100
  have eq2307139 : x = y := by
    first
    | (have r₁ := eq2306875
       have r₂ := eq27
       grind)
    | exact resolve eq2306875 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306875
  have eq2307230 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq2224549 eq2307075
    | exact resolve eq2307075 eq2224549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224549 eq2307075
  have eq2307304 : x = (k y y) := by
    first
    | (have r₁ := eq2307230
       have r₂ := eq2227531
       grind)
    | exact resolve eq2307230 eq2227531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227531 eq2307230
  have eq2307378 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2307139
       grind)
    | exact superpose eq2307139 eq24
    | exact resolve eq24 eq2307139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2308767 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2307378
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2307378
    | exact resolve eq2307378 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307378
  have eq2309017 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2225419 eq2308767
    | exact resolve eq2308767 eq2225419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308767
  have eq2325840 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2309017 eq2225515
    | exact resolve eq2225515 eq2309017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225515 eq2309017
  have eq2326469 : x = (k x x) := by
    first
    | (have i₁ := eq2307304
       have i₂ := eq2307139
       grind)
    | exact superpose eq2307139 eq2307304
    | exact resolve eq2307304 eq2307139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307139 eq2307304
  have eq2326554 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq873 x x
       have i₂ := eq2326469
       grind)
    | exact superpose eq2326469 eq873
    | (have j0 := eq873 x x
       grind)
    | exact resolve eq873 eq2326469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq2326469
  have eq2326575 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2326554
  have eq2326576 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2326575
  have eq2326602 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2326576
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2326576
    | exact resolve eq2326576 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2326576
  have eq2326678 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2225419 eq2326602
    | exact resolve eq2326602 eq2225419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225419 eq2326602
  have eq2334163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2326678 eq2325840
    | exact resolve eq2325840 eq2326678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325840 eq2326678
  have eq2334164 : False := by grind
  exact eq2334164

/-- `Equation1577`: `x = (y ◇ z) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pyx_pyy_pxy_Equation1577 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1577 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1577.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq27 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq35 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq603 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27
    | exact resolve eq27 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq657 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq603
    | (have j0 := eq603 X0 X1
       grind)
    | exact resolve eq603 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq2263 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq657 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq657 X0 X1
       grind)
    | exact superpose eq657 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq657 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq657 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq657 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq657 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq2268 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2263 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq2269 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268
  have eq2369 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2269 X1 X0
       grind)
    | exact superpose eq2269 eq10
    | (have j1 := eq2269 X1 X0
       grind)
    | exact resolve eq10 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2574 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2369 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2369
    | (have j0 := eq2369 X0 X1
       grind)
    | exact resolve eq2369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq2955 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2574 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2960 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2955 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq2955 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq2955 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq2955 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq2955 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq3098 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq3319 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3098 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098
  have eq3371 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3319 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319
  have eq3424 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3371 (σ X0)
       grind)
    | exact superpose eq3371 eq15
    | exact resolve eq15 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3430 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq3371 (τ X0)
       grind)
    | exact superpose eq3371 eq35
    | exact resolve eq35 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3477 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3430 X0
       have i₂ := eq3371 X0
       grind)
    | exact superpose eq3371 eq3430
    | exact resolve eq3430 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3430
  have eq3483 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3424 X0
       have i₂ := eq3371 X0
       grind)
    | exact superpose eq3371 eq3424
    | exact resolve eq3424 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371 eq3424
  have eq4142 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq4148 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (M.op (τ X0) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq3477 X0
       grind)
    | exact superpose eq3477 eq9
    | exact resolve eq9 eq3477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4163 : ∀ X0 : G, (τ (k (M.op X0 X0) X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4142 X0
       have i₂ := eq35 (M.op X0 X0) X0
       grind)
    | exact superpose eq35 eq4142
    | exact resolve eq4142 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4142
  have eq4207 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq4163
  have eq4278 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq4283 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2960 X1 (σ X0)
       have i₂ := eq3483 X0
       grind)
    | exact superpose eq3483 eq2960
    | (have j0 := eq2960 X1 (σ X0)
       grind)
    | exact resolve eq2960 eq3483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4284 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq3483 X0
       grind)
    | exact superpose eq3483 eq9
    | exact resolve eq9 eq3483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4296 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4278 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq4278
    | exact resolve eq4278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278
  have eq4302 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq4296
  have eq4416 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (M.op (M.op (τ (M.op X1 X1)) (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X1) X0) (τ (M.op X1 X1)) (τ X1)
       have i₂ := eq4148 X1 X0
       grind)
    | exact superpose eq4148 eq9
    | exact resolve eq9 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148
  have eq4574 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4284 X0 (σ X0)
       have i₂ := eq3483 X0
       grind)
    | exact superpose eq3483 eq4284
    | exact resolve eq4284 eq3483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4584 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (M.op (M.op (σ (M.op X1 X1)) (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (σ X1) X0) (σ (M.op X1 X1)) (σ X1)
       have i₂ := eq4284 X1 X0
       grind)
    | exact superpose eq4284 eq9
    | exact resolve eq9 eq4284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4284
  have eq4590 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4574 X0
       have i₂ := eq4302 X0
       grind)
    | exact superpose eq4302 eq4574
    | exact resolve eq4574 eq4302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4302 eq4574
  have eq4761 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (τ (M.op (σ X0) (σ X0))) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4416 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4416
    | exact resolve eq4416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4416
  have eq4828 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (τ (σ (M.op X0 X0))) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4761 X0 X1
       have i₂ := eq3483 X0
       grind)
    | exact superpose eq3483 eq4761
    | exact resolve eq4761 eq3483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4761
  have eq4830 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4828 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4828
    | exact resolve eq4828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828
  have eq4853 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq4830 X0 (M.op (M.op X0 X0) (M.op X0 X1))
       grind)
    | exact superpose eq4830 eq9
    | exact resolve eq9 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4926 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4853 X1 (M.op (M.op X1 X1) (M.op X1 X0))
       have i₂ := eq4853 X1 X0
       grind)
    | exact superpose eq4853 eq4853
    | exact resolve eq4853 eq4853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4951 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1 (M.op X1 X1)
       have i₂ := eq4853 X1 X0
       grind)
    | exact superpose eq4853 eq9
    | exact resolve eq9 eq4853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4953 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = (M.op (M.op X2 X2) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op X2 X0)) X1 X2
       have i₂ := eq4853 X2 X0
       grind)
    | exact superpose eq4853 eq9
    | exact resolve eq9 eq4853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4989 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = (M.op X2 (M.op (M.op X2 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4953 X0 X1 X2
       have i₂ := eq4926 X0 X2
       grind)
    | exact superpose eq4926 eq4953
    | exact resolve eq4953 eq4926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4953
  have eq4991 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4853 X0 X1
       have i₂ := eq4926 X1 X0
       grind)
    | exact superpose eq4926 eq4853
    | exact resolve eq4853 eq4926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4853 eq4926
  have eq5026 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4991 (σ X0) X1
       have i₂ := eq3483 X0
       grind)
    | exact superpose eq3483 eq4991
    | exact resolve eq4991 eq3483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5110 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (M.op (τ X0) (τ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4951 X1 (τ X0)
       have i₂ := eq3477 X0
       grind)
    | exact superpose eq3477 eq4951
    | exact resolve eq4951 eq3477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951
  have eq5177 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5110 X0 X1
       have i₂ := eq4207 X0
       grind)
    | exact superpose eq4207 eq5110
    | exact resolve eq5110 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5110
  have eq5210 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = (M.op (τ (M.op X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5177 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq4830 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq4830 eq5177
    | exact resolve eq5177 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177
  have eq5294 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = (M.op (τ (M.op X0 (M.op X0 (M.op (M.op X0 X0) X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5210 X0 X1
       have i₂ := eq4989 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq4989 eq5210
    | exact resolve eq5210 eq4989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5210
  have eq5327 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5294 X0 X1
       have i₂ := eq4991 X0 X0
       grind)
    | exact superpose eq4991 eq5294
    | exact resolve eq5294 eq4991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5294
  have eq5619 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5327 (σ X0) X1
       have i₂ := eq3483 X0
       grind)
    | exact superpose eq3483 eq5327
    | exact resolve eq5327 eq3483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5327
  have eq5714 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5619 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5619
    | exact resolve eq5619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5619
  have eq6263 : ∀ X0 : G, (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))) = (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq4207 (M.op (σ (M.op x x)) (σ x))
       have i₂ := eq4584 (M.op (σ (M.op x x)) (σ x)) x
       grind)
    | exact superpose eq4584 eq4207
    | exact resolve eq4207 eq4584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4207
  have eq6319 : ∀ X0 : G, (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))) = (M.op X0 (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq6263 X0
       have i₂ := eq5714 X0 (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))
       grind)
    | exact superpose eq5714 eq6263
    | exact resolve eq6263 eq5714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6263
  have eq6366 : ∀ X0 : G, (τ (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))) = (M.op X0 (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq6319 X0
       have i₂ := eq4584 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))) X0
       grind)
    | exact superpose eq4584 eq6319
    | exact resolve eq6319 eq4584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4584 eq6319
  have eq6384 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq6366 X0
       have i₂ := eq5026 X0 (σ X0)
       grind)
    | exact superpose eq5026 eq6366
    | exact resolve eq6366 eq5026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5026 eq6366
  have eq6387 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq6384 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6384
    | exact resolve eq6384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6384
  have eq6406 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))))) := by
    intro X0
    first
    | (have i₁ := eq4590 (M.op (M.op X0 X0) X0)
       have i₂ := eq4830 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq4830 eq4590
    | exact resolve eq4590 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830
  have eq6432 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op X0 (M.op (M.op X0 X0) X0))))) := by
    intro X0
    first
    | (have i₁ := eq6406 X0
       have i₂ := eq4989 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq4989 eq6406
    | exact resolve eq6406 eq4989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6406
  have eq6453 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6432 X0
       have i₂ := eq4991 X0 X0
       grind)
    | exact superpose eq4991 eq6432
    | exact resolve eq6432 eq4991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4991 eq6432
  have eq8261 : ∀ X0 : G, (τ (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ (M.op X0 X0)) (σ X0)))) = (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq3477 (M.op (σ (M.op X0 X0)) (σ X0))
       have i₂ := eq5714 X0 (τ (M.op (σ (M.op X0 X0)) (σ X0)))
       grind)
    | exact superpose eq5714 eq3477
    | exact resolve eq3477 eq5714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477
  have eq8280 : ∀ X0 : G, (σ (τ (M.op (σ (M.op X0 X0)) (σ X0)))) = (M.op (σ (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0))))) (σ (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0))))))) := by
    intro X0
    first
    | (have i₁ := eq4590 (τ (M.op (σ (M.op X0 X0)) (σ X0)))
       have i₂ := eq5714 X0 (τ (M.op (σ (M.op X0 X0)) (σ X0)))
       grind)
    | exact superpose eq5714 eq4590
    | exact resolve eq4590 eq5714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4590
  have eq8349 : ∀ X0 : G, (σ (τ (M.op (σ (M.op X0 X0)) (σ X0)))) = (M.op (σ (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0))))) (σ (M.op X0 (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0))))))) := by
    intro X0
    first
    | (have i₁ := eq8280 X0
       have i₂ := eq5714 X0 (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0))))
       grind)
    | exact superpose eq5714 eq8280
    | exact resolve eq8280 eq5714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5714 eq8280
  have eq8363 : ∀ X0 : G, (τ (M.op (σ X0) (M.op (M.op (σ X0) (σ X0)) (σ X0)))) = (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq8261 X0
       have i₂ := eq4989 (σ X0) (σ (M.op X0 X0)) (σ X0)
       grind)
    | exact superpose eq4989 eq8261
    | exact resolve eq8261 eq4989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4989 eq8261
  have eq8412 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0))))) (σ (M.op X0 (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0))))))) := by
    intro X0
    first
    | (have i₁ := eq8349 X0
       have i₂ := eq11 (M.op (σ (M.op X0 X0)) (σ X0))
       grind)
    | exact superpose eq11 eq8349
    | exact resolve eq8349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8349
  have eq8419 : ∀ X0 : G, (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq8363 X0
       have i₂ := eq3483 X0
       grind)
    | exact superpose eq3483 eq8363
    | exact resolve eq8363 eq3483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3483 eq8363
  have eq8468 : ∀ X0 : G, (M.op X0 (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq6387 X0
       have i₂ := eq8419 X0
       grind)
    | exact superpose eq8419 eq6387
    | exact resolve eq6387 eq8419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387 eq8419
  have eq8506 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0))))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8412 X0
       have i₂ := eq8468 X0
       grind)
    | exact superpose eq8468 eq8412
    | exact resolve eq8412 eq8468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8412
  have eq8588 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (τ (M.op (σ (M.op X0 X0)) (σ X0))) X0 X0
       have i₂ := eq8468 X0
       grind)
    | exact superpose eq8468 eq9
    | exact resolve eq9 eq8468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8468
  have eq8666 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8506 X0
       have i₂ := eq8588 X0
       grind)
    | exact superpose eq8588 eq8506
    | exact resolve eq8506 eq8588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8506 eq8588
  have eq8730 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8666 X0
       have i₂ := eq6453 X0
       grind)
    | exact superpose eq6453 eq8666
    | exact resolve eq8666 eq6453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6453 eq8666
  have eq9867 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq4283 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq4283 X0 (σ X0)
       grind)
    | exact superpose eq4283 eq10
    | (have j1 := eq4283 X1 X0
       grind)
    | exact resolve eq10 eq4283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq10986 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq9867 (σ X0) X1
       grind)
    | exact superpose eq9867 eq15
    | (have j1 := eq9867 (σ X0) X1
       grind)
    | exact resolve eq15 eq9867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9867
  have eq11027 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10986 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10986
    | (have j0 := eq10986 X0 X1
       grind)
    | exact resolve eq10986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10986
  have eq12399 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11027 x y
       grind)
    | exact superpose eq11027 eq16
    | (have j1 := eq11027 x y
       grind)
    | exact resolve eq16 eq11027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11027
  have eq12655 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12399
       have i₂ := eq2960 x y
       grind)
    | exact superpose eq2960 eq12399
    | (have j1 := eq2960 x y
       grind)
    | exact resolve eq12399 eq2960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960 eq12399
  have eq12671 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq12655
  have eq12672 : x = (M.op y y) := by grind
  clear eq12671
  have eq12713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8730 y
       have i₂ := eq12672
       grind)
    | exact superpose eq12672 eq8730
    | exact resolve eq8730 eq12672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8730 eq12672
  have eq12747 : False := by grind
  exact eq12747

/-- `Equation1586`: `x = (y ◇ z) ◇ (z ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_y_pyx_Equation1586 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1586 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1586.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X0 X0))) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq124 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq174 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op X0 X0))) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 X0)) (M.op X3 X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op x X2) (M.op X2 (M.op X0 X0))
       have i₂ := eq16 X0 x X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 (M.op X2 (M.op X0 X0))
       have i₂ := eq16 X0 X2 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq180 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq174 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq174
    | exact resolve eq174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq175 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq188 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq185
    | exact resolve eq185 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq542 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op x y) (M.op y (σ y)))) := by
    intro X0
    first
    | exact superpose eq188 eq16
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq16 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq563 X0 X1 X2
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq563
    | exact resolve eq563 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq587 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X2 (M.op (M.op x y) (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X2
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq619 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq577 eq16
    | exact resolve eq16 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq874 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq885 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq897 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq897 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq897 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq897 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq957 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq883
       grind)
    | exact superpose eq883 eq39
    | exact resolve eq39 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq957
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq957
    | exact resolve eq957 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq960 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq958
    | exact resolve eq958 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq960 eq885
    | exact resolve eq885 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq968
       have r₂ := eq27
       grind)
    | exact resolve eq968 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq981 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq975 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq975
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq975
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq975
       grind)
    | exact resolve eq12 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq986 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq981
  have eq988 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq986
    | exact resolve eq986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq989 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq988
  have eq1001 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq989 eq107
    | exact resolve eq107 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1008 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1001
    | exact resolve eq1001 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1011 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq883 eq1008
    | exact resolve eq1008 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq1008
  have eq1012 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1011
  have eq1017 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1012
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq1012
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq1012 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1019 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1012
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1012
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1012
       grind)
    | exact resolve eq12 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1012
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1012
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1012
       grind)
    | exact resolve eq13 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1023 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1021
  have eq1024 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1019
  have eq1025 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1023
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1023
    | exact resolve eq1023 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1026 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1024
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1024
    | exact resolve eq1024 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1027 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1026
  have eq1028 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1017
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq1017
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq1017
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1017 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1029 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1028
       have r₂ := eq872
       grind)
    | exact resolve eq1028 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1030 : y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1012 eq1029
    | exact resolve eq1029 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq1029
  have eq1032 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1025
       grind)
    | exact superpose eq1025 eq40
    | exact resolve eq40 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1033 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1032
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1032
    | exact resolve eq1032 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1035 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1033
    | exact resolve eq1033 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1039 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq1027
       grind)
    | exact superpose eq1027 eq36
    | exact resolve eq36 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1027
  have eq1044 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1039
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1039
    | exact resolve eq1039 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1061 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1044 eq885
    | exact resolve eq885 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1065 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1061
  have eq1073 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1065
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq1065
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq1065 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1065 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1065
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1065
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1065
       grind)
    | exact resolve eq13 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1079 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1077
  have eq1081 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1079
    | exact resolve eq1079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1082 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq1073
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq1073
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq1073
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq1073 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1035 eq1081
    | exact resolve eq1081 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq1081
  have eq1084 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1082
       have r₂ := eq874
       grind)
    | exact resolve eq1082 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq1082
  have eq1085 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1083
       have r₂ := eq27
       grind)
    | exact resolve eq1083 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1086 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1085 eq27
    | exact resolve eq27 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1085 eq180
    | (have r₁ := eq180
       have r₂ := eq1085
       grind)
    | exact resolve eq180 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1090 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op x y) (M.op y (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1085 eq542
    | exact resolve eq542 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq1093 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1088
  have eq1103 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1093 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1093
       grind)
    | exact resolve eq13 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1109 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1103
    | exact resolve eq1103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1114 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1085 eq1109
    | exact resolve eq1109 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1132 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1030 eq37
    | exact resolve eq37 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1030
  have eq1135 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1132
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1132
    | exact resolve eq1132 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1137 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1085 eq1135
    | exact resolve eq1135 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1140 : (τ (σ y)) = (k (M.op x y) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1137 eq124
    | exact resolve eq124 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1137
  have eq1143 : y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq31 eq1140
    | exact resolve eq1140 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1156 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1084 eq90
    | exact resolve eq90 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq1163 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq31 eq1156
    | exact resolve eq1156 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1168 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1163 eq1093
    | exact resolve eq1093 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1169 : (M.op (M.op x y) (M.op y (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1163 eq188
    | exact resolve eq188 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1163 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1163
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1163
       grind)
    | exact resolve eq13 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1174 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq1172
  have eq1176 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq1168
  have eq1178 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq1174
    | exact resolve eq1174 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1180 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op y (σ x))) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1085 eq1169
    | exact resolve eq1169 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1182 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1085 eq1178
    | exact resolve eq1178 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1183 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op y (σ x))) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq1180
    | exact resolve eq1180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1184 : (σ x) = (M.op (M.op x y) (M.op y (σ x))) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1085 eq1183
    | exact resolve eq1183 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1198 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1176 eq960
    | exact resolve eq960 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1203 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1176 eq141
    | exact resolve eq141 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1176
  have eq1208 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq1198
  have eq1212 : y = (k y x) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq31 eq1203
    | exact resolve eq1203 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1214 : y = (k x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1208
       have r₂ := eq872
       grind)
    | exact resolve eq1208 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1292 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0)))) = (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq577 eq177
    | exact resolve eq177 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1297 : ∀ X0 : G, (M.op (M.op y y) (M.op y y)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 y X0 x
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1375 : ∀ X0 : G, (M.op (M.op x y) (M.op y y)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1297 X0
       have i₂ := eq619 y y y
       grind)
    | exact superpose eq619 eq1297
    | (have j1 := eq619 y X0 x
       grind)
    | exact resolve eq1297 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1380 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq587 eq1292
    | exact resolve eq1292 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1423 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq925 y x
       have i₂ := eq1214
       grind)
    | exact superpose eq1214 eq925
    | (have j0 := eq925 y x
       grind)
    | (have r₁ := eq925 y x
       have r₂ := eq1214
       grind)
    | exact resolve eq925 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1428 : y ≠ y ∨ (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1143 eq925
    | (have j0 := eq925 y (M.op x y)
       grind)
    | (have r₁ := eq925 y (M.op x y)
       have r₂ := eq1143
       grind)
    | exact resolve eq925 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1447 : y ≠ y ∨ (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1428
  have eq1448 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1447
  have eq1451 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1423
  have eq1452 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1451
  have eq1457 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1452
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1452
    | exact resolve eq1452 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1463 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1457
       grind)
    | exact superpose eq1457 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1457
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1457
       grind)
    | exact resolve eq13 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq1468 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1463
  have eq1472 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1468
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1468
    | exact resolve eq1468 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1480 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq40
    | exact resolve eq40 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1484 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1480
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1480
    | exact resolve eq1480 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480
  have eq1486 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq1484
    | exact resolve eq1484 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1508 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1486 eq1182
    | exact resolve eq1182 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182 eq1486
  have eq1517 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1508
  have eq1524 : x = (M.op x y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1517
       have r₂ := eq1086
       grind)
    | exact resolve eq1517 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq1528 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1472 eq1524
    | exact resolve eq1524 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472 eq1524
  have eq1530 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1528 eq28
    | exact resolve eq28 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1528
  have eq1556 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1530
    | exact resolve eq1530 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1530
  have eq1557 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1556
  have eq1560 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1557
       grind)
    | exact superpose eq1557 eq18
    | exact resolve eq18 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1561 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1557
       grind)
    | exact superpose eq1557 eq24
    | exact resolve eq24 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq1557
       grind)
    | exact superpose eq1557 eq174
    | exact resolve eq174 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1573 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1212
       have i₂ := eq1557
       grind)
    | exact superpose eq1557 eq1212
    | exact resolve eq1212 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1583 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq1573
  have eq1592 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1561
    | exact resolve eq1561 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1605 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1592 eq1086
    | exact resolve eq1086 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1607 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq1605
  have eq1845 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1448 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq1448
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq1448
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1448
       grind)
    | exact resolve eq13 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1850 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1845
  have eq2496 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq1583 eq39
    | exact resolve eq39 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq2506 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq20 eq2496
    | exact resolve eq2496 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq2508 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq1592 eq2506
    | exact resolve eq2506 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592 eq2506
  have eq2573 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq2508 eq1114
    | (have r₁ := eq1114
       have r₂ := eq2508
       grind)
    | exact resolve eq1114 eq2508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq2508
  have eq2584 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq2573
  have eq2585 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq2584
  have eq2652 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq2585 eq1084
    | exact resolve eq1084 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084 eq2585
  have eq2665 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq2652
  have eq2676 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have r₁ := eq2665
       have r₂ := eq1607
       grind)
    | exact resolve eq2665 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq2727 : (M.op (M.op x y) (M.op y (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq2676 eq188
    | exact resolve eq188 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq2676
  have eq2744 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op y (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq1085 eq2727
    | exact resolve eq2727 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727
  have eq2749 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op y (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq26 eq2744
    | exact resolve eq2744 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744
  have eq2750 : (σ x) = (M.op (M.op x y) (M.op y (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq1085 eq2749
    | exact resolve eq2749 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2751 : (σ x) = (M.op (M.op x y) (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq1557 eq2750
    | exact resolve eq2750 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq2871 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op y (σ y))) (M.op (M.op x y) (M.op y (σ y)))) (M.op (M.op (M.op x y) (M.op y (σ y))) (M.op (M.op x y) (M.op y (σ y))))) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1090 eq177
    | exact resolve eq177 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq2884 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq587 eq2871
    | exact resolve eq2871 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871
  have eq3661 : y ≠ (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1850
  have eq3682 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1184 eq2884
    | exact resolve eq2884 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq2884
  have eq3694 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by grind
  clear eq3682
  have eq3709 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq3694
    | exact resolve eq3694 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3694
  have eq3723 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq1085 eq3709
    | exact resolve eq3709 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq3709
  have eq3734 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq1557 eq3723
    | exact resolve eq3723 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723
  have eq3825 : (σ y) = (M.op (M.op x y) (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq3734 eq1564
    | exact resolve eq1564 eq3734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564 eq3734
  have eq3837 : (σ y) = (M.op (M.op x y) (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq3825
  have eq3847 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq2751 eq3837
    | exact resolve eq3837 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751 eq3837
  have eq3861 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3847
       have r₂ := eq1607
       grind)
    | exact resolve eq3847 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607 eq3847
  have eq3878 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3861 eq925
    | (have j0 := eq925 (M.op x y) x
       grind)
    | (have r₁ := eq925 (M.op x y) x
       have r₂ := eq3861
       grind)
    | exact resolve eq925 eq3861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3861
  have eq3879 : x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq3878
  have eq3881 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1560 eq3879
    | exact resolve eq3879 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560 eq3879
  have eq3882 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq3881
  have eq3897 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) (M.op y x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3882 eq577
    | exact resolve eq577 eq3882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3902 : x = (M.op (M.op x y) (M.op y (M.op y x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3897 x
       have i₂ := eq619 (M.op y x) x sF0
       grind)
    | exact superpose eq619 eq3897
    | exact resolve eq3897 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq3909 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1557 eq3902
    | exact resolve eq3902 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3902
  have eq3912 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3882 eq3909
    | exact resolve eq3909 eq3882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3909
  have eq4041 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3912 eq178
    | exact resolve eq178 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq4066 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1375 eq4041
    | exact resolve eq4041 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375 eq4041
  have eq4071 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1557 eq4066
    | exact resolve eq4066 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557 eq4066
  have eq4076 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3912 eq4071
    | exact resolve eq4071 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4071
  have eq4080 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4076 eq3912
    | exact resolve eq3912 eq4076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912 eq4076
  have eq4116 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq4080
  have eq4129 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3882 eq4116
    | exact resolve eq4116 eq3882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3882 eq4116
  have eq4130 : x = (M.op x y) := by grind
  clear eq4129
  have eq4139 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4130
       grind)
    | exact superpose eq4130 eq18
    | exact resolve eq18 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4140 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4130
       grind)
    | exact superpose eq4130 eq22
    | exact resolve eq22 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4141 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq4130
       grind)
    | exact superpose eq4130 eq35
    | exact resolve eq35 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq4142 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq4130
       grind)
    | exact superpose eq4130 eq39
    | exact resolve eq39 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq4143 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq179
       have i₂ := eq4130
       grind)
    | exact superpose eq4130 eq179
    | (have r₁ := eq179
       have r₂ := eq4130
       grind)
    | exact resolve eq179 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq4144 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq872
       have i₂ := eq4130
       grind)
    | exact superpose eq4130 eq872
    | (have r₁ := eq872
       have r₂ := eq4130
       grind)
    | exact resolve eq872 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq4147 : y = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq4144
  have eq4148 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq4143
  have eq4150 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4140 eq20
    | exact resolve eq20 eq4140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4266 : ∀ X0 : G, (M.op (M.op y y) (M.op y y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4139 eq177
    | exact resolve eq177 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4273 : ∀ X0 : G, (M.op (M.op x y) (M.op y y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq4266 X0
       have i₂ := eq619 y y y
       grind)
    | exact superpose eq619 eq4266
    | exact resolve eq4266 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4266
  have eq4281 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op x y) (k y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq4148 eq577
    | exact resolve eq577 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4285 : y ≠ (k y (M.op x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq4148 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | exact resolve eq13 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4287 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (k y (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq4148 eq177
    | exact resolve eq177 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4290 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (k y (M.op x y))) (M.op (M.op x y) (k y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4148 eq577
    | exact resolve eq577 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4294 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op (k y (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq4287 X0
       have i₂ := eq619 X0 X0 X0
       grind)
    | exact superpose eq619 eq4287
    | exact resolve eq4287 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4287
  have eq4295 : y ≠ (k y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq4139 eq4285
    | exact resolve eq4285 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285
  have eq4994 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq4147 eq4141
    | exact resolve eq4141 eq4147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4141 eq4147
  have eq5007 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq4994
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4994
    | exact resolve eq4994 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994
  have eq5011 : (σ y) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq4148 eq5007
    | exact resolve eq5007 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5007
  have eq5036 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5011 eq948
    | (have j0 := eq948 (σ x) (σ y)
       grind)
    | (have r₁ := eq948 (σ x) (σ y)
       have r₂ := eq5011
       grind)
    | exact resolve eq948 eq5011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq5037 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5011 eq925
    | (have j0 := eq925 (σ y) (σ x)
       grind)
    | (have r₁ := eq925 (σ y) (σ x)
       have r₂ := eq5011
       grind)
    | exact resolve eq925 eq5011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq5011
  have eq5038 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by grind
  clear eq5037
  have eq5039 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq5036
  have eq5042 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq5038
    | exact resolve eq5038 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038
  have eq5043 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq5039
    | exact resolve eq5039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039
  have eq5049 : y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5043
    | exact resolve eq5043 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5043
  have eq5079 : (M.op (M.op x y) (M.op y y)) = (M.op (k y (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq4148 eq4273
    | exact resolve eq4273 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273
  have eq5166 : y ≠ y ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5049 eq4295
    | (have r₁ := eq4295
       have r₂ := eq5049
       grind)
    | exact resolve eq4295 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4295
  have eq5172 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5049 eq4142
    | exact resolve eq4142 eq5049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4142 eq5049
  have eq5182 : (M.op x y) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5166
  have eq5187 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5172
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5172
    | exact resolve eq5172 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5172
  have eq5239 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5182 eq40
    | exact resolve eq40 eq5182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5182
  have eq5250 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5239
    | exact resolve eq5239 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5239
  have eq5255 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4150 eq5250
    | exact resolve eq5250 eq4150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq5269 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5187 eq885
    | exact resolve eq885 eq5187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq5187
  have eq5291 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5269
  have eq5363 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5291 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq5291
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5291
       grind)
    | exact resolve eq13 eq5291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291
  have eq5372 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5363
  have eq5376 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5372
    | exact resolve eq5372 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5372
  have eq5381 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5255 eq5376
    | exact resolve eq5376 eq5255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5255 eq5376
  have eq5382 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5381
  have eq5392 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5382
  have eq5998 : ∀ X2 : G, (M.op (M.op x y) (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op X2 X2))) = X2 := by
    intro X2
    first
    | exact superpose eq4281 eq16
    | exact resolve eq16 eq4281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6000 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op (M.op x y) (k y (M.op x y)))) (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op (M.op x y) (k y (M.op x y))))) = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op x y)))) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq4281 eq177
    | exact resolve eq177 eq4281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq6010 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op (M.op x y) (k y (M.op x y)))) (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op (M.op x y) (k y (M.op x y))))) := by
    first
    | (have i₁ := eq6000 x x x
       have i₂ := eq1380 sF0 x x x
       grind)
    | exact superpose eq1380 eq6000
    | exact resolve eq6000 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380 eq6000
  have eq6016 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (k y (M.op x y))))) := by
    first
    | (have i₁ := eq6010
       have i₂ := eq619 (M.op sF0 (k y sF0)) (M.op sF0 (k y sF0)) (M.op sF0 (k y sF0))
       grind)
    | exact superpose eq619 eq6010
    | exact resolve eq6010 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6010
  have eq6499 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5042 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq5042
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq5042
       grind)
    | exact resolve eq12 eq5042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042
  have eq6510 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq6499
  have eq6514 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq6510
    | exact resolve eq6510 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6510
  have eq6515 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq6514
  have eq6605 : ∀ X0 : G, (M.op (k y (M.op x y)) X0) = (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq5998 eq4294
    | exact resolve eq4294 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6612 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) X0) = (M.op (M.op (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op X0 X0)) (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op X0 X0))) (M.op (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op X0 X0)) (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq5998 eq177
    | exact resolve eq177 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5998
  have eq6619 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) X0) = (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6612 X0 X1
       have i₂ := eq619 (M.op (M.op sF0 (k y sF0)) (M.op X0 X0)) (M.op (M.op sF0 (k y sF0)) (M.op X0 X0)) (M.op (M.op sF0 (k y sF0)) (M.op X0 X0))
       grind)
    | exact superpose eq619 eq6612
    | exact resolve eq6612 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6612
  have eq6633 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) X0) = (M.op (k y (M.op x y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq6605 eq6619
    | exact resolve eq6619 eq6605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6605 eq6619
  have eq6646 : ∀ X0 : G, (M.op (k y (M.op x y)) X0) = (M.op (M.op (M.op x y) (M.op y y)) X0) := by
    intro X0
    first
    | exact superpose eq5079 eq6633
    | exact resolve eq6633 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6633
  have eq7362 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq6515 eq107
    | exact resolve eq107 eq6515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq6515
  have eq7376 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq29 eq7362
    | exact resolve eq7362 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7362
  have eq7384 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq7376
       have i₂ := eq4130
       grind)
    | exact superpose eq4130 eq7376
    | exact resolve eq7376 eq4130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4130 eq7376
  have eq7404 : ∀ X0 : G, (M.op y (M.op (k y (M.op x y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq6646 eq176
    | exact resolve eq176 eq6646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq6646
  have eq7512 : (M.op (M.op x y) (k y (M.op x y))) = (M.op y (M.op (k y (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq4290 eq7404
    | exact resolve eq7404 eq4290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7533 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op (M.op (M.op (k y (M.op x y)) (M.op X0 X0)) (M.op (k y (M.op x y)) (M.op X0 X0))) (M.op (M.op (k y (M.op x y)) (M.op X0 X0)) (M.op (k y (M.op x y)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq7404 eq177
    | exact resolve eq177 eq7404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7535 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op x y) X0)) = (M.op (k y (M.op x y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq7404 eq577
    | exact resolve eq577 eq7404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq7540 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op (M.op x y) (M.op y (M.op (k y (M.op x y)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7533 X0 X1
       have i₂ := eq619 (M.op (k y sF0) (M.op X0 X0)) (M.op (k y sF0) (M.op X0 X0)) (M.op (k y sF0) (M.op X0 X0))
       grind)
    | exact superpose eq619 eq7533
    | exact resolve eq7533 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq7533
  have eq7549 : (M.op (M.op x y) (k y (M.op x y))) = (M.op y (M.op (M.op x y) (M.op y y))) := by
    first
    | exact superpose eq5079 eq7512
    | exact resolve eq7512 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7512
  have eq7555 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | exact superpose eq7404 eq7540
    | exact resolve eq7540 eq7404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7540
  have eq7676 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq7384 eq6016
    | exact resolve eq6016 eq7384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7384
  have eq7701 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq174 eq7676
    | exact resolve eq7676 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq7676
  have eq8149 : ∀ X0 : G, (M.op (M.op X0 y) (M.op (M.op x y) (k y (M.op x y)))) = (M.op (M.op (M.op (M.op x y) (M.op y y)) (M.op (M.op x y) (M.op y y))) (M.op (M.op (M.op x y) (M.op y y)) (M.op (M.op x y) (M.op y y)))) := by
    intro X0
    first
    | exact superpose eq7549 eq177
    | exact resolve eq177 eq7549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq7549
  have eq8161 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 y) (M.op (M.op x y) (k y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq587 eq8149
    | exact resolve eq8149 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq8149
  have eq8174 : (M.op y y) = (M.op (M.op x y) (M.op (M.op x y) (k y (M.op x y)))) := by
    first
    | (have i₁ := eq8161 x
       have i₂ := eq7555 (M.op sF0 (k y sF0)) x
       grind)
    | (have i₁ := eq8161 x
       have i₂ := eq7555 (M.op sF0 (k y sF0)) x
       grind)
    | exact superpose eq7555 eq8161
    | (have j0 := eq8161 x
       grind)
    | exact resolve eq8161 eq7555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7555 eq8161
  have eq8184 : (M.op (M.op x y) (M.op y (M.op (M.op x y) (k y (M.op x y))))) = (M.op (k y (M.op x y)) (M.op y y)) := by
    first
    | exact superpose eq8174 eq4294
    | exact resolve eq4294 eq8174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4294
  have eq8207 : (M.op (M.op x y) (M.op x y)) = (M.op (k y (M.op x y)) (M.op y y)) := by
    first
    | exact superpose eq6016 eq8184
    | exact resolve eq8184 eq6016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6016 eq8184
  have eq8226 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq8207 eq7404
    | exact resolve eq7404 eq8207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7404
  have eq8266 : y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq7701 eq8226
    | exact resolve eq8226 eq7701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7701 eq8226
  have eq8307 : y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8266
       have r₂ := eq3661
       grind)
    | exact resolve eq8266 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661 eq8266
  have eq8314 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4148 eq8307
    | exact resolve eq8307 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8307
  have eq8327 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8314 eq4290
    | exact resolve eq4290 eq8314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4290
  have eq8331 : (M.op (M.op x y) (M.op y y)) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8314 eq5079
    | exact resolve eq5079 eq8314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5079
  have eq8344 : (M.op y y) = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8314 eq8174
    | exact resolve eq8174 eq8314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8174
  have eq8366 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4139 eq8344
    | exact resolve eq8344 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139 eq8344
  have eq8376 : (k y (M.op x y)) = (M.op (M.op x y) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4148 eq8331
    | exact resolve eq8331 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148 eq8331
  have eq8377 : (M.op x y) = (M.op (k y (M.op x y)) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7535 eq8327
    | exact resolve eq8327 eq7535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7535 eq8327
  have eq8386 : y = (M.op (M.op x y) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8314 eq8376
    | exact resolve eq8376 eq8314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8314 eq8376
  have eq8387 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8207 eq8377
    | exact resolve eq8377 eq8207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8207 eq8377
  have eq8390 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8366 eq8386
    | exact resolve eq8386 eq8366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8366 eq8386
  have eq8392 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8387 eq8390
    | exact resolve eq8390 eq8387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8390
  have eq8393 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8387 eq8392
    | exact resolve eq8392 eq8387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8387 eq8392
  have eq8395 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8393 eq27
    | exact resolve eq27 eq8393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8393
  have eq8404 : y = (M.op x y) := by
    first
    | (have r₁ := eq8395
       have r₂ := eq4150
       grind)
    | exact resolve eq8395 eq4150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8395
  have eq8406 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8404
       grind)
    | exact superpose eq8404 eq24
    | exact resolve eq24 eq8404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8404
  have eq8499 : (σ x) = (σ y) := by
    first
    | exact superpose eq4140 eq8406
    | exact resolve eq8406 eq4140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4140 eq8406
  have eq8596 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8499 eq5392
    | (have r₁ := eq5392
       have r₂ := eq8499
       grind)
    | exact resolve eq5392 eq8499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5392 eq8499
  have eq8602 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8596
  have eq8661 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8602 eq27
    | exact resolve eq27 eq8602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8602
  have eq8676 : False := by grind
  exact eq8676

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pyy_pyx_Equation1590 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1590 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
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
  clear eq75
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq113 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq113 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq113 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq119 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq114 sF2
       grind)
    | exact superpose eq114 eq49
    | exact resolve eq49 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq119
    | exact resolve eq119 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq255 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
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
  have eq256 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq603 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X3 (M.op X0 X3))) (M.op X0 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X3 (M.op X0 X3))
       have i₂ := eq56 (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq738 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X3 X2 (M.op X2 (M.op X3 X0))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) X0)) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) X0))
       have i₂ := eq52 x X2 X1 X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq766 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op y X0)) = (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) X0))
       have i₂ := eq52 x X2 X1 X0
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq769 : ∀ X0 X1 X2 : G, (σ y) = (M.op X0 (M.op (M.op (M.op X1 (M.op X2 (σ x))) (M.op (M.op X2 X1) X0)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X2 (M.op X1 sF2)) (M.op (M.op X1 X2) x))
       have i₂ := eq52 sF2 X1 X2 x
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq770 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op X1 (M.op X2 (σ x))) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X2 (M.op X1 sF2)) (M.op (M.op X1 X2) x))
       have i₂ := eq52 sF2 X1 X2 x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq818 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X2) (M.op (M.op (M.op X1 X0) X3) X4)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op (M.op X1 X0) X3) (M.op X3 X2) X5
       have i₂ := eq55 X2 X1 X0 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X1)) = (M.op (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq256 eq55
    | exact resolve eq55 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq834 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1)) = (M.op (M.op (σ x) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq270 eq55
    | exact resolve eq55 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq851 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X3 (M.op X4 X0)) X2 X1 (M.op X4 X3)
       have i₂ := eq14 X0 X4 X3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X2) (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X3 X2) (M.op (M.op X1 X0) X3) X4 X5
       have i₂ := eq55 X2 X1 X0 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq895 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op (M.op (M.op X1 X0) X3) X4)) = (M.op (M.op X1 X2) (M.op X0 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq818 X0 X1 X2 X3 X4 x
       have i₂ := eq55 X4 X0 (M.op X1 X2) x
       grind)
    | exact superpose eq55 eq818
    | exact resolve eq818 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq818
  have eq1150 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq393 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq393
    | exact resolve eq393 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq393
  have eq1186 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (k (τ X0) (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1150 X0
       have i₂ := eq114 sF2
       grind)
    | exact superpose eq114 eq1150
    | exact resolve eq1150 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1190 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1186 X0
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq1186
    | exact resolve eq1186 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq9757 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op X0 (M.op (M.op x y) X0))) y) := by
    intro X0
    first
    | exact superpose eq255 eq603
    | exact resolve eq603 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq9768 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq269 eq603
    | exact resolve eq603 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq17975 : ∀ X1 X2 : G, y = (M.op (M.op X1 (M.op X2 x)) (M.op (M.op X2 X1) (M.op x y))) := by
    intro X1 X2
    first
    | (have i₁ := eq765 X1 X1 X2
       have i₂ := eq738 sF0 X1 (M.op X1 (M.op X2 x)) (M.op X2 X1)
       grind)
    | exact superpose eq738 eq765
    | exact resolve eq765 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq19209 : ∀ X1 X2 : G, (σ y) = (M.op (M.op X1 (M.op X2 (σ x))) (M.op (M.op X2 X1) (M.op (σ x) (σ y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq769 X1 X1 X2
       have i₂ := eq738 sF4 X1 (M.op X1 (M.op X2 sF2)) (M.op X2 X1)
       grind)
    | exact superpose eq738 eq769
    | exact resolve eq769 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq769
  have eq48560 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X2) (M.op (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) (M.op X3 X5))) = X5 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq884 X0 X1 X2 X3 x X5
       have i₂ := eq895 X3 (M.op X1 X0) (M.op X0 (M.op X1 X2)) x X5
       grind)
    | exact superpose eq895 eq884
    | exact resolve eq884 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884 eq895
  have eq48561 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 X2) (M.op X0 (M.op X1 (M.op (M.op X1 X2) (M.op X0 (M.op X3 X5)))))) = X5 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq48560 X0 X1 X2 X3 X5
       have i₂ := eq851 (M.op X3 X5) X0 X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq851 eq48560
    | exact resolve eq48560 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq48560
  have eq73430 : (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (k x x) (M.op x x)) := by
    first
    | exact superpose eq49 eq1190
    | exact resolve eq1190 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1190
  have eq73474 : (k (M.op x x) (M.op x x)) = (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq73430
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq73430
    | exact resolve eq73430 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73430
  have eq73485 : (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq73474
       have i₂ := eq114 sF2
       grind)
    | exact superpose eq114 eq73474
    | exact resolve eq73474 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73474
  have eq73492 : (M.op (M.op x x) (M.op x x)) = (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq73485
       have i₂ := eq114 (M.op x x)
       grind)
    | exact superpose eq114 eq73485
    | exact resolve eq73485 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73485
  have eq73499 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq73492
       have i₂ := eq114 (M.op sF2 sF2)
       grind)
    | exact superpose eq114 eq73492
    | exact resolve eq73492 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq73492
  have eq73506 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) := by
    first
    | exact superpose eq834 eq73499
    | exact resolve eq73499 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq73499
  have eq73512 : (M.op (M.op x y) (M.op y x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq73506
       have i₂ := eq833 x x
       grind)
    | exact superpose eq833 eq73506
    | exact resolve eq73506 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq73506
  have eq73523 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) = (σ (M.op (M.op x y) (M.op y x))) := by
    first
    | exact superpose eq73512 eq15
    | exact resolve eq15 eq73512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159470 : ∀ X0 X1 X2 : G, y = (M.op (M.op y X0) (M.op X1 (M.op X2 (M.op (M.op X2 X0) (M.op X1 (M.op y x)))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48561 X1 X2 X0 y y
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq48561
    | exact resolve eq48561 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq159478 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq159470 x x x
       have i₂ := eq48561 x x x y x
       grind)
    | (have i₁ := eq159470 x x x
       have i₂ := eq48561 x x x x (M.op (M.op y x) (M.op x (M.op x (M.op (M.op x x) (M.op x (M.op y x))))))
       grind)
    | exact superpose eq48561 eq159470
    | exact resolve eq159470 eq48561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159470
  have eq159599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq159478 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq159478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159478
  have eq159612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq159599
    | exact resolve eq159599 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159599
  have eq159623 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq159612
       have r₂ := eq27
       grind)
    | exact resolve eq159612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159612
  have eq159627 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq159623
    | exact resolve eq159623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159623
  have eq159771 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op X2 (M.op (M.op X2 X0) (M.op X1 (M.op (σ y) (σ x))))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq159627 eq48561
    | exact resolve eq48561 eq159627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159627
  have eq159779 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq159771 x x x
       have i₂ := eq48561 x x x sF3 sF2
       grind)
    | (have i₁ := eq159771 x x x
       have i₂ := eq48561 x x x x (M.op (M.op sF3 x) (M.op x (M.op x (M.op (M.op x x) (M.op x (M.op sF3 sF2))))))
       grind)
    | exact superpose eq48561 eq159771
    | exact resolve eq159771 eq48561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48561 eq159771
  have eq159979 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op X1 X0) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq159779 eq19209
    | exact resolve eq19209 eq159779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19209 eq159779
  have eq159992 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq770 eq159979
    | exact resolve eq159979 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq159979
  have eq167466 : (τ (σ y)) = (M.op (M.op x y) (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq159992 eq73512
    | exact resolve eq73512 eq159992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73512 eq159992
  have eq167720 : y = (M.op (M.op x y) (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq167466
    | exact resolve eq167466 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167466
  have eq188382 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 (M.op (M.op x y) X0))) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq167720 eq603
    | exact resolve eq603 eq167720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167720
  have eq188597 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9757 eq188382
    | exact resolve eq188382 eq9757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9757 eq188382
  have eq188598 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq188597
  have eq188694 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq188598 eq29
    | exact resolve eq29 eq188598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq188598
  have eq188977 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq188694
    | exact resolve eq188694 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq188694
  have eq188978 : x = (M.op x y) ∨ x = y := by grind
  clear eq188977
  have eq189006 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq188978 eq20
    | exact resolve eq20 eq188978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189166 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 x)) (M.op (M.op X1 X0) x)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq188978 eq17975
    | exact resolve eq17975 eq188978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17975 eq188978
  have eq189181 : y = (M.op (M.op x y) (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq189166 x x
       have i₂ := eq766 x x x
       grind)
    | exact superpose eq766 eq189166
    | exact resolve eq189166 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq189166
  have eq189288 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq189006
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq189006
    | exact resolve eq189006 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189006
  have eq190710 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq189181 eq73523
    | exact resolve eq73523 eq189181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73523 eq189181
  have eq190976 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq190710
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq190710
    | exact resolve eq190710 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190710
  have eq199764 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq190976 eq603
    | exact resolve eq603 eq190976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq190976
  have eq199987 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq9768 eq199764
    | exact resolve eq199764 eq9768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9768 eq199764
  have eq200077 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq199987 eq27
    | exact resolve eq27 eq199987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199987
  have eq200261 : x = y := by
    first
    | (have r₁ := eq200077
       have r₂ := eq189288
       grind)
    | exact resolve eq200077 eq189288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189288 eq200077
  have eq200274 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq200261
       grind)
    | exact superpose eq200261 eq18
    | exact resolve eq18 eq200261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq200275 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq200261
       grind)
    | exact superpose eq200261 eq24
    | exact resolve eq24 eq200261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq200261
  have eq200551 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq200275
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq200275
    | exact resolve eq200275 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq200275
  have eq200600 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq200551 eq26
    | exact resolve eq26 eq200551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq200551
  have eq201393 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq200600 eq120
    | exact resolve eq120 eq200600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq200600
  have eq201696 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq201393
       have i₂ := eq200274
       grind)
    | exact superpose eq200274 eq201393
    | exact resolve eq201393 eq200274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200274 eq201393
  have eq201784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq201696 eq15
    | exact resolve eq15 eq201696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201696
  have eq201868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq201784
    | exact resolve eq201784 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq201784
  have eq201889 : False := by grind
  exact eq201889

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyx_pxx_pyy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq101 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq39527 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op x X0) X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq14
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq39586 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq39527 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq39527
    | exact resolve eq39527 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39527
  have eq39626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq39586 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq39586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39586
  have eq39635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq39626
    | exact resolve eq39626 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39626
  have eq39646 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq39635
       have r₂ := eq27
       grind)
    | exact resolve eq39635 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39635
  have eq39650 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq39646
    | exact resolve eq39646 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39646
  have eq39665 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) X0) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39650 eq14
    | exact resolve eq14 eq39650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39650
  have eq39724 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq39665 x
       have i₂ := eq14 sF2 sF2 x
       grind)
    | exact superpose eq14 eq39665
    | exact resolve eq39665 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39665
  have eq39787 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39724 eq14
    | exact resolve eq14 eq39724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39724
  have eq39820 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq51 eq39787
    | exact resolve eq39787 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq39787
  have eq39821 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq39820
  have eq40088 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq39821
       grind)
    | exact superpose eq39821 eq14
    | exact resolve eq14 eq39821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39821
  have eq40121 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq50 eq40088
    | exact resolve eq40088 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq40088
  have eq40122 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq40121
  have eq40146 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq40122 eq29
    | exact resolve eq29 eq40122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40122
  have eq40297 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq40146
    | exact resolve eq40146 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq40146
  have eq40298 : x = y := by grind
  clear eq40297
  have eq40320 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq40298
       grind)
    | exact superpose eq40298 eq18
    | exact resolve eq18 eq40298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq40321 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq40298
       grind)
    | exact superpose eq40298 eq24
    | exact resolve eq24 eq40298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq40298
  have eq40479 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40321
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40321
    | exact resolve eq40321 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq40321
  have eq40513 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40479 eq26
    | exact resolve eq26 eq40479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40479
  have eq40813 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq40513 eq72
    | exact resolve eq72 eq40513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq40513
  have eq40897 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40813
       have i₂ := eq40320
       grind)
    | exact superpose eq40320 eq40813
    | exact resolve eq40813 eq40320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40320 eq40813
  have eq41608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40897 eq15
    | exact resolve eq15 eq40897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40897
  have eq41698 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq41608
    | exact resolve eq41608 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41608
  have eq41719 : False := by grind
  exact eq41719

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pyy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq44 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq44 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq85 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq85
    | exact resolve eq85 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq85
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq176 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq195 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq176
       have i₂ := eq97 y
       grind)
    | exact superpose eq97 eq176
    | exact resolve eq176 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq738 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq690
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq690
    | (have j1 := eq58 y x
       grind)
    | exact resolve eq690 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq690
  have eq739 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq738
  have eq4947 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (M.op (σ y) X0) X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq739
       grind)
    | exact superpose eq739 eq9
    | exact resolve eq9 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq4974 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4947 x
       have i₂ := eq195 y x
       grind)
    | exact superpose eq195 eq4947
    | exact resolve eq4947 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq4947
  have eq5157 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4974
       grind)
    | exact superpose eq4974 eq10
    | exact resolve eq10 eq4974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4974
  have eq5206 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5157
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5157
    | exact resolve eq5157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5157
  have eq5316 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5206
       grind)
    | exact superpose eq5206 eq16
    | exact resolve eq16 eq5206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206
  have eq5317 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq5316
       have r₂ := eq97 x
       grind)
    | exact resolve eq5316 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5316
  have eq5330 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq5317
       grind)
    | exact superpose eq5317 eq9
    | exact resolve eq9 eq5317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5317
  have eq5364 : x = y := by
    first
    | (have i₁ := eq5330 x
       have i₂ := eq9 x y x
       grind)
    | exact superpose eq9 eq5330
    | exact resolve eq5330 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330
  have eq5536 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5364
       grind)
    | exact superpose eq5364 eq16
    | exact resolve eq16 eq5364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5364
  have eq5538 : False := by grind
  exact eq5538

/-- `Equation1663`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_pyy_pyx_Equation1663 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1663 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1663.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) = X0 := by
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
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x (M.op (M.op x x) x)
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 y x
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
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
  have eq104 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq105 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq107 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq104
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq124 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq105
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq16
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq124
  have eq149 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq173 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq149 eq16
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4950 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq85 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85
    | (have j0 := eq85 x
       grind)
    | exact resolve eq85 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq4969 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4950
  have eq4977 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4969
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4969
    | exact resolve eq4969 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4969
  have eq4995 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4977
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq4977 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4977
  have eq4999 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4995 eq49
    | exact resolve eq49 eq4995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq4995
  have eq5193 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq107
    | (have j0 := eq107 y
       grind)
    | exact resolve eq107 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq5210 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5193
  have eq5216 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5210
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq5210
    | exact resolve eq5210 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq5210
  have eq5241 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5216
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5216 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5271 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5241 eq129
    | exact resolve eq129 eq5241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq5483 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq150
    | (have j0 := eq150 (M.op x y)
       grind)
    | exact resolve eq150 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq5499 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5483
  have eq5504 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq149 eq5499
    | exact resolve eq5499 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq5499
  have eq5536 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5504
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5504 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504
  have eq5585 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5536 eq173
    | exact resolve eq173 eq5536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq5536
  have eq13944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13944
    | exact resolve eq13944 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13944
  have eq13963 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq13952
       have r₂ := eq27
       grind)
    | exact resolve eq13952 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13952
  have eq13965 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13963
    | exact resolve eq13963 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13963
  have eq13972 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13965 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13965
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13965
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13965
       grind)
    | exact resolve eq12 eq13965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13979 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13965 eq56
    | exact resolve eq56 eq13965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13965
  have eq13988 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq13972
  have eq13995 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13988
    | exact resolve eq13988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13988
  have eq13996 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq13995
  have eq14732 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13979 eq4999
    | exact resolve eq4999 eq13979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13979
  have eq14775 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq14732
    | exact resolve eq14732 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14732
  have eq15933 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13996 eq123
    | exact resolve eq123 eq13996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq13996
  have eq15949 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15933
  have eq16375 : (τ (σ (M.op x y))) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15949 eq4999
    | exact resolve eq4999 eq15949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4999 eq15949
  have eq16423 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq16375
    | exact resolve eq16375 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16375
  have eq17559 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14775
       have i₂ := eq16423
       grind)
    | exact superpose eq16423 eq14775
    | exact resolve eq14775 eq16423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14775 eq16423
  have eq17578 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17559
  have eq17635 : x ≠ x ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq17578
       grind)
    | exact superpose eq17578 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17578
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17578
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17578
       grind)
    | exact resolve eq12 eq17578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17636 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq17578
       grind)
    | exact superpose eq17578 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17578
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17578
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17578
       grind)
    | exact resolve eq13 eq17578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17642 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq17578
       grind)
    | exact superpose eq17578 eq56
    | exact resolve eq56 eq17578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17578
  have eq17652 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17636
  have eq17653 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17635
  have eq17660 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17652
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17652
    | exact resolve eq17652 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17652
  have eq17661 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17653
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17653
    | exact resolve eq17653 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17653
  have eq17662 : (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17661
  have eq17706 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq17660
       grind)
    | exact superpose eq17660 eq44
    | exact resolve eq44 eq17660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq17660
  have eq17739 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq17706
    | exact resolve eq17706 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17706
  have eq19976 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq17662
       grind)
    | exact superpose eq17662 eq104
    | exact resolve eq104 eq17662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq17662
  have eq20134 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5241 eq130
    | exact resolve eq130 eq5241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq5241
  have eq20813 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19976
       have i₂ := eq17642
       grind)
    | exact superpose eq17642 eq19976
    | exact resolve eq19976 eq17642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17642 eq19976
  have eq20865 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20813
  have eq20872 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20865
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20865
    | exact resolve eq20865 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20865
  have eq20889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20872 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq20872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20872
  have eq20903 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20889
  have eq20909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq20903
    | exact resolve eq20903 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20903
  have eq20910 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20909
  have eq20929 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20910 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20910
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20910
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20910
       grind)
    | exact resolve eq13 eq20910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20910
  have eq20947 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20929
  have eq20954 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq20947
    | exact resolve eq20947 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20947
  have eq21399 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20954 eq17739
    | exact resolve eq17739 eq20954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17739 eq20954
  have eq21411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21399
  have eq21415 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21411
       have r₂ := eq27
       grind)
    | exact resolve eq21411 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21411
  have eq21422 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21415 eq58
    | exact resolve eq58 eq21415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq21415
  have eq21439 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21422 eq5271
    | exact resolve eq5271 eq21422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271 eq21422
  have eq21487 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq21439
    | exact resolve eq21439 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21439
  have eq21580 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq21487
       grind)
    | exact superpose eq21487 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq21487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21599 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq21580
  have eq26722 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq21599
       grind)
    | exact superpose eq21599 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq21599
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21599
       grind)
    | exact resolve eq13 eq21599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26739 : x ≠ y ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq21599
  have eq26740 : y = (k y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq26722
  have eq26896 : x = y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21487
       have i₂ := eq26740
       grind)
    | exact superpose eq26740 eq21487
    | exact resolve eq21487 eq26740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21487 eq26740
  have eq26928 : x = y ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq26896
  have eq26948 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26928
       have r₂ := eq26739
       grind)
    | exact resolve eq26928 eq26739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26739 eq26928
  have eq26999 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq26948
       grind)
    | exact superpose eq26948 eq56
    | exact resolve eq56 eq26948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26948
  have eq27015 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26999
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26999
    | exact resolve eq26999 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq26999
  have eq27016 : y = (M.op x y) := by grind
  clear eq27015
  have eq27025 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27016 eq20
    | exact resolve eq20 eq27016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27029 : x = (M.op y y) := by
    first
    | exact superpose eq27016 eq57
    | exact resolve eq57 eq27016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq27156 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq27025
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27025
    | exact resolve eq27025 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27025
  have eq27214 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq27156 eq26
    | exact resolve eq26 eq27156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27419 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq27029
       grind)
    | exact superpose eq27029 eq13
    | exact resolve eq13 eq27029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29276 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20134
       have i₂ := eq27029
       grind)
    | exact superpose eq27029 eq20134
    | exact resolve eq20134 eq27029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20134
  have eq29277 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27156 eq29276
    | exact resolve eq29276 eq27156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29276
  have eq29278 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq29277
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29277
    | exact resolve eq29277 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29277
  have eq29279 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq29278
       have i₂ := eq27029
       grind)
    | exact superpose eq27029 eq29278
    | exact resolve eq29278 eq27029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27029 eq29278
  have eq29280 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq29279 eq5585
    | exact resolve eq5585 eq29279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29298 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq29279 eq56
    | exact resolve eq56 eq29279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq29279
  have eq29312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27214 eq29298
    | exact resolve eq29298 eq27214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27214 eq29298
  have eq29326 : (τ (σ x)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27016 eq29280
    | exact resolve eq29280 eq27016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29280
  have eq29327 : x = y := by
    first
    | (have r₁ := eq29312
       have r₂ := eq27
       grind)
    | exact resolve eq29312 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29312
  have eq29335 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq28 eq29326
    | exact resolve eq29326 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq29326
  have eq29339 : x = (k y y) := by
    first
    | (have r₁ := eq29335
       have r₂ := eq27419
       grind)
    | exact resolve eq29335 eq27419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27419 eq29335
  have eq29341 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq29327
       grind)
    | exact superpose eq29327 eq24
    | exact resolve eq24 eq29327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29532 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq27156 eq29341
    | exact resolve eq29341 eq27156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29341
  have eq29609 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq29532
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29532
    | exact resolve eq29532 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29532
  have eq29703 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29609 eq26
    | exact resolve eq26 eq29609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq29895 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27156 eq29703
    | exact resolve eq29703 eq27156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27156 eq29703
  have eq30036 : x = (k x x) := by
    first
    | (have i₁ := eq29339
       have i₂ := eq29327
       grind)
    | exact superpose eq29327 eq29339
    | exact resolve eq29339 eq29327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29339
  have eq30248 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29895 eq5585
    | exact resolve eq5585 eq29895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5585 eq29895
  have eq30294 : (k y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27016 eq30248
    | exact resolve eq30248 eq27016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27016 eq30248
  have eq30308 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30294
       have i₂ := eq29327
       grind)
    | exact superpose eq29327 eq30294
    | exact resolve eq30294 eq29327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29327 eq30294
  have eq30316 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30308
       have i₂ := eq30036
       grind)
    | exact superpose eq30036 eq30308
    | exact resolve eq30308 eq30036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30036 eq30308
  have eq30332 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30316 eq15
    | exact resolve eq15 eq30316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30316
  have eq30410 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30332
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30332
    | exact resolve eq30332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq30332
  have eq30442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29609 eq30410
    | exact resolve eq30410 eq29609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29609 eq30410
  have eq30462 : False := by grind
  exact eq30462
