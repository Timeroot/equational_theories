import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  clear eq36
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq92 y x
       grind)
    | exact superpose eq92 eq71
    | (have j1 := eq92 y x
       grind)
    | exact resolve eq71 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ y) (σ x)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  have eq351 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq127
  have eq352 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq351
  have eq355 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq352 eq118
    | exact resolve eq118 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq359 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq355
  have eq364 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq359
       have r₂ := eq129
       grind)
    | exact resolve eq359 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq359
  have eq376 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq364 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq364
       grind)
    | exact resolve eq13 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq377 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq451 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq377 eq118
    | exact resolve eq118 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq377
  have eq887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq884
  have eq894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq887
    | exact resolve eq887 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq896 : x = (M.op x y) := by
    first
    | (have r₁ := eq894
       have r₂ := eq27
       grind)
    | exact resolve eq894 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq898 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq896 eq20
    | exact resolve eq20 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq896 eq53
    | exact resolve eq53 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq907 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq896 eq218
    | exact resolve eq218 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq914 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq898
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq898
    | exact resolve eq898 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq915 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq914 eq26
    | exact resolve eq26 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1010 : x = (M.op x x) := by
    first
    | (have i₁ := eq901 x
       have i₂ := eq451 x
       grind)
    | exact superpose eq451 eq901
    | exact resolve eq901 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq901
  have eq1022 : y = (M.op x y) := by
    first
    | (have i₁ := eq907
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq907
    | exact resolve eq907 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq1036 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1010
       grind)
    | exact resolve eq13 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1037 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1036 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1040 : y = (M.op x y) := by
    first
    | (have i₁ := eq1022
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1022
    | exact resolve eq1022 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1041 : x = y := by
    first
    | exact superpose eq896 eq1040
    | exact resolve eq1040 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq1040
  have eq1044 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1041
       grind)
    | exact superpose eq1041 eq24
    | exact resolve eq24 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1041
  have eq1062 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1044
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1044
    | exact resolve eq1044 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1044
  have eq1069 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq914 eq1062
    | exact resolve eq1062 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1103 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1069 eq915
    | exact resolve eq915 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq1153 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1037 y
       grind)
    | exact superpose eq1037 eq71
    | exact resolve eq71 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1037
  have eq1158 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq914 eq1153
    | exact resolve eq1153 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq1153
  have eq1162 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1069 eq1158
    | exact resolve eq1158 eq1069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069 eq1158
  have eq1165 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1162
    | exact resolve eq1162 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1162
  have eq1168 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1165
    | exact resolve eq1165 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1165
  have eq1176 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1168 eq92
    | (have j0 := eq92 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1168
  have eq1177 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1176
  have eq1179 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1103 eq1177
    | exact resolve eq1177 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq1177
  have eq1182 : False := by grind
  exact eq1182

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4) X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X4 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0
       have i₂ := eq51 X0 X1 X2 X3
       grind)
    | exact superpose eq51 eq9
    | exact resolve eq9 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq51
    | exact resolve eq51 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq427 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq526 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq368 y x
       grind)
    | exact superpose eq368 eq16
    | (have j1 := eq368 y x
       grind)
    | exact resolve eq16 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq368 X0 X0
       grind)
    | exact superpose eq368 eq67
    | (have j1 := eq368 X0 X0
       grind)
    | exact resolve eq67 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq368
  have eq557 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq528 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq1153 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq557 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq557
    | exact resolve eq557 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1153 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1153
    | (have j0 := eq1153 X0
       grind)
    | exact resolve eq1153 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1153
  have eq1187 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1183 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1183
    | (have j0 := eq1183 X0
       grind)
    | exact resolve eq1183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1194 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1187 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1187
    | (have j0 := eq1187 (τ X0)
       grind)
    | exact resolve eq1187 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1187
  have eq1547 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X1) X0) X5)) X6) X1) X6) = X6 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq68 X1 (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X0 X5 X6
       have i₂ := eq51 X0 X2 X3 X4
       grind)
    | exact superpose eq51 eq68
    | exact resolve eq68 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq68
  have eq6028 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq526
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq526
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq526 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq6031 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq6028
  have eq25302 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq86 (σ x) (σ y)
       have i₂ := eq6031
       grind)
    | exact superpose eq6031 eq86
    | exact resolve eq86 eq6031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6031
  have eq25387 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq25302
  have eq25457 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq25387
       grind)
    | exact superpose eq25387 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq25387
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq25387
       grind)
    | exact resolve eq12 eq25387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25387
  have eq25594 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq25457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25457
  have eq25693 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1194 (σ x)
       have i₂ := eq25594 (σ x)
       grind)
    | exact superpose eq25594 eq1194
    | (have j0 := eq1194 (σ x)
       grind)
    | exact resolve eq1194 eq25594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq25594
  have eq25762 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq25693
  have eq25799 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq25762
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25762
    | exact resolve eq25762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25762
  have eq25800 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq25799
  have eq25850 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq86 x y
       have i₂ := eq25800
       grind)
    | exact superpose eq25800 eq86
    | exact resolve eq86 eq25800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25800
  have eq25935 : x = (M.op x x) := by grind
  clear eq25850
  have eq25990 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq25935
       grind)
    | exact superpose eq25935 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq25935
       grind)
    | exact resolve eq12 eq25935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25994 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq25935
       grind)
    | exact superpose eq25935 eq73
    | exact resolve eq73 eq25935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq26079 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq427 x x x
       have i₂ := eq25935
       grind)
    | exact superpose eq25935 eq427
    | exact resolve eq427 eq25935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26127 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq25990 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25990
  have eq26141 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq26079 X0
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq26079
    | exact resolve eq26079 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq26079
  have eq26200 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq557 x
       have i₂ := eq26127 x
       grind)
    | exact superpose eq26127 eq557
    | (have j0 := eq557 x
       grind)
    | exact resolve eq557 eq26127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq26127
  have eq26292 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq26200
  have eq31953 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25994 X0
       have i₂ := eq26141 X0
       grind)
    | exact superpose eq26141 eq25994
    | exact resolve eq25994 eq26141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25994
  have eq31956 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq26141 X0
       have i₂ := eq31953 X0
       grind)
    | exact superpose eq31953 eq26141
    | exact resolve eq26141 eq31953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26141
  have eq32049 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq427 x X1 X0
       have i₂ := eq31953 X0
       grind)
    | exact superpose eq31953 eq427
    | exact resolve eq427 eq31953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq32364 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32049 X0 X0
       have i₂ := eq31953 X0
       grind)
    | exact superpose eq31953 eq32049
    | exact resolve eq32049 eq31953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32049
  have eq36191 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op (M.op x (M.op (M.op x (M.op x X1)) X2)) X0) x) X3)) X4) X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1547 x X0 x X1 X2 X3 X4
       have i₂ := eq25935
       grind)
    | exact superpose eq25935 eq1547
    | exact resolve eq1547 eq25935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547 eq25935
  have eq36585 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op x X3)) X4) X0) X4) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq36191 X0 x x X3 X4
       have i₂ := eq31956 (M.op (M.op x (M.op (M.op x (M.op x x)) x)) X0)
       grind)
    | exact superpose eq31956 eq36191
    | exact resolve eq36191 eq31956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31956 eq36191
  have eq36596 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X3) X4) X0) X4) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq36585 X0 X3 X4
       have i₂ := eq31953 X3
       grind)
    | exact superpose eq31953 eq36585
    | exact resolve eq36585 eq31953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36585
  have eq38856 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36596 (σ x) (σ x) X0
       have i₂ := eq26292
       grind)
    | exact superpose eq26292 eq36596
    | exact resolve eq36596 eq26292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26292 eq36596
  have eq39373 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq38856 X0
       have i₂ := eq32364 X0 (σ x)
       grind)
    | exact superpose eq32364 eq38856
    | exact resolve eq38856 eq32364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32364 eq38856
  have eq39870 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39373 (σ y)
       grind)
    | exact superpose eq39373 eq16
    | exact resolve eq16 eq39373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39373
  have eq40282 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq39870
       have i₂ := eq31953 y
       grind)
    | exact superpose eq31953 eq39870
    | exact resolve eq39870 eq31953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31953 eq39870
  have eq40283 : False := by grind
  exact eq40283

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_y_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4) X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X4 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq61
    | exact resolve eq61 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq269 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq170 y x
       grind)
    | exact superpose eq170 eq16
    | (have j1 := eq170 y x
       grind)
    | exact resolve eq16 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq170 X0 X0
       grind)
    | exact superpose eq170 eq67
    | (have j1 := eq170 X0 X0
       grind)
    | exact resolve eq67 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq276 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq170 X0 X1
       grind)
    | exact superpose eq170 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq170 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq170 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq170 X0 X1
       grind)
    | exact resolve eq13 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq289 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq291 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq294 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq289 X0 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq289 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq289 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq298 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq585 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1243 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X1) X0) X5)) X6) X1) X6) = X6 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq68 X1 (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X0 X5 X6
       have i₂ := eq61 X0 X2 X3 X4
       grind)
    | exact superpose eq61 eq68
    | exact resolve eq68 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq68
  have eq1408 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq291 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq291
    | exact resolve eq291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq1444 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1408 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1408
    | (have j0 := eq1408 X0
       grind)
    | exact resolve eq1408 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1408
  have eq1448 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1444 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1444
    | (have j0 := eq1444 X0
       grind)
    | exact resolve eq1444 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444
  have eq1455 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1448 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1448
    | (have j0 := eq1448 (τ X0)
       grind)
    | exact resolve eq1448 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1448
  have eq5638 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq269
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq269
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq269 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq5641 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq5638
  have eq21760 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq86 (σ x) (σ y)
       have i₂ := eq5641
       grind)
    | exact superpose eq5641 eq86
    | exact resolve eq86 eq5641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5641
  have eq21838 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq21760
  have eq21907 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq21838
       grind)
    | exact superpose eq21838 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq21838
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq21838
       grind)
    | exact resolve eq12 eq21838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21838
  have eq22035 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21907 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21907
  have eq22129 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1455 (σ x)
       have i₂ := eq22035 (σ x)
       grind)
    | exact superpose eq22035 eq1455
    | (have j0 := eq1455 (σ x)
       grind)
    | exact resolve eq1455 eq22035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455 eq22035
  have eq22208 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq22129
  have eq22236 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22208
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22208
    | exact resolve eq22208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22208
  have eq22237 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq22236
  have eq22683 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq86 x y
       have i₂ := eq22237
       grind)
    | exact superpose eq22237 eq86
    | exact resolve eq86 eq22237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22237
  have eq22763 : x = (M.op x x) := by grind
  clear eq22683
  have eq23229 : ∀ X0 : G, x ≠ x ∨ x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq22763
       grind)
    | exact superpose eq22763 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq22763
       grind)
    | exact resolve eq12 eq22763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23233 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq22763
       grind)
    | exact superpose eq22763 eq73
    | exact resolve eq73 eq22763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq23330 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq585 x x x
       have i₂ := eq22763
       grind)
    | exact superpose eq22763 eq585
    | exact resolve eq585 eq22763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23361 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq23229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23229
  have eq23370 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq23330 X0
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq23330
    | exact resolve eq23330 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq23330
  have eq23467 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq298 x x
       have i₂ := eq23361 x
       grind)
    | exact superpose eq23361 eq298
    | (have j0 := eq298 x x
       grind)
    | exact resolve eq298 eq23361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq23361
  have eq23510 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq23467
  have eq23511 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq23510
  have eq26791 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23233 X0
       have i₂ := eq23370 X0
       grind)
    | exact superpose eq23370 eq23233
    | exact resolve eq23233 eq23370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23233
  have eq27235 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq23370 X0
       have i₂ := eq26791 X0
       grind)
    | exact superpose eq26791 eq23370
    | exact resolve eq23370 eq26791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23370
  have eq27350 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq585 x X1 X0
       have i₂ := eq26791 X0
       grind)
    | exact superpose eq26791 eq585
    | exact resolve eq585 eq26791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq27603 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27350 X0 X0
       have i₂ := eq26791 X0
       grind)
    | exact superpose eq26791 eq27350
    | exact resolve eq27350 eq26791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27350
  have eq31202 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op (M.op x (M.op (M.op x (M.op x X1)) X2)) X0) x) X3)) X4) X0) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1243 x X0 x X1 X2 X3 X4
       have i₂ := eq22763
       grind)
    | exact superpose eq22763 eq1243
    | exact resolve eq1243 eq22763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243 eq22763
  have eq31568 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op x X3)) X4) X0) X4) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq31202 X0 x x X3 X4
       have i₂ := eq27235 (M.op (M.op x (M.op (M.op x (M.op x x)) x)) X0)
       grind)
    | exact superpose eq27235 eq31202
    | exact resolve eq31202 eq27235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27235 eq31202
  have eq31579 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X3) X4) X0) X4) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq31568 X0 X3 X4
       have i₂ := eq26791 X3
       grind)
    | exact superpose eq26791 eq31568
    | exact resolve eq31568 eq26791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31568
  have eq33317 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31579 (σ x) (σ x) X0
       have i₂ := eq23511
       grind)
    | exact superpose eq23511 eq31579
    | exact resolve eq31579 eq23511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23511 eq31579
  have eq33790 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq33317 X0
       have i₂ := eq27603 X0 (σ x)
       grind)
    | exact superpose eq27603 eq33317
    | exact resolve eq33317 eq27603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27603 eq33317
  have eq34270 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33790 (σ y)
       grind)
    | exact superpose eq33790 eq16
    | exact resolve eq16 eq33790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33790
  have eq34665 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq34270
       have i₂ := eq26791 y
       grind)
    | exact superpose eq26791 eq34270
    | exact resolve eq34270 eq26791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26791 eq34270
  have eq34666 : False := by grind
  exact eq34666

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq61 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq64 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
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
  clear eq23 eq37
  have eq75 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq117
    | exact resolve eq117 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq427 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq62
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq433 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq427 X0
       grind)
    | exact superpose eq427 eq14
    | exact resolve eq14 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq607 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq94 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq608 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq900 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq433
    | exact resolve eq433 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq63 eq433
    | exact resolve eq433 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq64 eq433
    | exact resolve eq433 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq1014 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x X0) (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (M.op x X0)
       have i₂ := eq900 x X0
       grind)
    | exact superpose eq900 eq63
    | exact resolve eq63 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1019 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq64 (M.op sF2 x)
       have i₂ := eq900 sF2 x
       grind)
    | exact superpose eq900 eq64
    | exact resolve eq64 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq3524 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq608 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq608
    | (have j0 := eq608 (τ X0)
       grind)
    | exact resolve eq608 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq608
  have eq3532 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3524 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3524
    | (have j0 := eq3524 X0
       grind)
    | exact resolve eq3524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq3538 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3532 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3532
    | (have j0 := eq3532 X0
       grind)
    | exact resolve eq3532 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq21941 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq21948 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq21941
    | exact resolve eq21941 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21941
  have eq21959 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21948
       have r₂ := eq28
       grind)
    | exact resolve eq21948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21948
  have eq21983 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21959 eq75
    | exact resolve eq75 eq21959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21959
  have eq22026 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq21983
       have r₂ := eq13 x (σ x)
       grind)
    | (have r₁ := eq21983
       have r₂ := eq13 x x
       grind)
    | exact resolve eq21983 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21983
  have eq22032 : (τ (σ y)) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22026 eq80
    | exact resolve eq80 eq22026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq22026
  have eq22055 : y = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq22032
    | exact resolve eq22032 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq22032
  have eq22059 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq22055
       have r₂ := eq13 x x
       grind)
    | exact resolve eq22055 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22055
  have eq22061 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq22059
       grind)
    | exact superpose eq22059 eq72
    | exact resolve eq72 eq22059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22070 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq22059
       grind)
    | exact superpose eq22059 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq22059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22059
  have eq22077 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq22070
  have eq22085 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22077
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22077
    | exact resolve eq22077 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22077
  have eq22094 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22061
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22061
    | exact resolve eq22061 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22061
  have eq26159 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq900 x x
       have i₂ := eq22085
       grind)
    | exact superpose eq22085 eq900
    | exact resolve eq900 eq22085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22085
  have eq26166 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26159
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26159
    | exact resolve eq26159 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26159
  have eq26167 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq26166
  have eq26174 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq60 x
       have i₂ := eq26167
       grind)
    | exact superpose eq26167 eq60
    | exact resolve eq60 eq26167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq26191 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1014 x
       have i₂ := eq26167
       grind)
    | exact superpose eq26167 eq1014
    | exact resolve eq1014 eq26167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq26167
  have eq26256 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq903 eq26191
    | exact resolve eq26191 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq26191
  have eq27701 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26256 eq26174
    | exact resolve eq26174 eq26256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26174 eq26256
  have eq27739 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq27701
  have eq27742 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27739
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27739
    | exact resolve eq27739 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq27739
  have eq27743 : y = (M.op x y) := by grind
  clear eq27742
  have eq27744 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27743 eq21
    | exact resolve eq21 eq27743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq27743
  have eq27901 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq27744
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27744
    | exact resolve eq27744 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27744
  have eq27908 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq27901 eq27
    | exact resolve eq27 eq27901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq27915 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27901 eq61
    | exact resolve eq61 eq27901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq27996 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27901 eq22094
    | exact resolve eq22094 eq27901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22094
  have eq28889 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27996 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq27996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27996
  have eq28896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27908 eq28889
    | exact resolve eq28889 eq27908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28889
  have eq28907 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq28896
       have r₂ := eq28
       grind)
    | exact resolve eq28896 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28896
  have eq55265 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28907 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq28907
       grind)
    | exact resolve eq13 eq28907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28907
  have eq55317 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq55265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55265
  have eq56922 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq900 X0 x
       have i₂ := eq55317 (M.op X0 x)
       grind)
    | exact superpose eq55317 eq900
    | (have j1 := eq55317 X0
       grind)
    | exact resolve eq900 eq55317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55317
  have eq56941 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq27908 eq56922
    | (have j0 := eq56922 X0
       grind)
    | exact resolve eq56922 eq27908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56922
  have eq56951 : ∀ X0 : G, y = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq56941 X0
       grind)
    | (have r₁ := eq56941 X0
       have r₂ := eq28
       grind)
    | exact resolve eq56941 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56941
  have eq56985 : ∀ X0 : G, y = (k y x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 x
       have i₂ := eq56951 X0
       grind)
    | exact superpose eq56951 eq75
    | (have j1 := eq56951 X0
       grind)
    | exact resolve eq75 eq56951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq56951
  have eq57072 : ∀ X0 : G, (σ y) = (k (σ y) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq72
       have i₂ := eq56985 X0
       grind)
    | exact superpose eq56985 eq72
    | (have j1 := eq56985 (σ y)
       grind)
    | exact resolve eq72 eq56985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq56985
  have eq57112 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27901 eq57072
    | (have j0 := eq57072 X0
       grind)
    | exact resolve eq57072 eq27901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57072
  have eq57131 : ∀ X0 : G, (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq57112 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq57112
    | (have j0 := eq57112 X0
       grind)
    | exact resolve eq57112 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq57112
  have eq57145 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27901 eq57131
    | (have j0 := eq57131 (σ (M.op x y))
       grind)
    | exact resolve eq57131 eq27901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27901 eq57131
  have eq57716 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq57145 (k X0 x)
       grind)
    | exact superpose eq57145 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       have j1 := eq57145 X0
       grind)
    | exact resolve eq11 eq57145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57145
  have eq57725 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq57716 X0
       have j1 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq57716 X0
       have r₂ := eq13 X0 (σ x)
       grind)
    | exact resolve eq57716 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57716
  have eq57736 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27908 eq57725
    | (have j0 := eq57725 X0
       grind)
    | exact resolve eq57725 eq27908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57725
  have eq57747 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq57736 X0
       grind)
    | (have r₁ := eq57736 X0
       have r₂ := eq28
       grind)
    | exact resolve eq57736 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57736
  have eq57989 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq900 X0 x
       have i₂ := eq57747 (M.op X0 x)
       grind)
    | exact superpose eq57747 eq900
    | (have j1 := eq57747 X0
       grind)
    | exact resolve eq900 eq57747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq57747
  have eq58005 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27908 eq57989
    | (have j0 := eq57989 X0
       grind)
    | exact resolve eq57989 eq27908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57989
  have eq58015 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq58005 X0
       grind)
    | (have r₁ := eq58005 X0
       have r₂ := eq28
       grind)
    | exact resolve eq58005 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58005
  have eq58083 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq58015 eq3538
    | (have j0 := eq3538 (σ x)
       grind)
    | (have r₁ := eq3538 (σ x)
       have r₂ := eq58015 (σ x)
       grind)
    | exact resolve eq3538 eq58015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538 eq58015
  have eq58135 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq58083
  have eq58384 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq58135 eq1019
    | exact resolve eq1019 eq58135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq58385 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq58135 eq27915
    | exact resolve eq27915 eq58135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27915 eq58135
  have eq58459 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq906 eq58384
    | exact resolve eq58384 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq58384
  have eq60174 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq58459 eq58385
    | exact resolve eq58385 eq58459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58385 eq58459
  have eq60175 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27908 eq60174
    | exact resolve eq60174 eq27908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27908 eq60174
  have eq60176 : False := by grind
  exact eq60176

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq186 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq187 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq207 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq211 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq207 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq207
    | exact resolve eq207 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq207 X0
       grind)
    | exact superpose eq207 eq9
    | exact resolve eq9 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq247 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq9
    | exact resolve eq9 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq279 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq217
    | exact resolve eq217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq304 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq279 X0 X1
       grind)
    | exact superpose eq279 eq9
    | exact resolve eq9 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq187 x y
       grind)
    | exact superpose eq187 eq16
    | (have j1 := eq187 x y
       grind)
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq20965 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq186 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq186
    | exact resolve eq186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq21086 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20965 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20965
    | (have j0 := eq20965 X0 X1
       grind)
    | exact resolve eq20965 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20965
  have eq32339 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1958
       have i₂ := eq21086 x y
       grind)
    | exact superpose eq21086 eq1958
    | (have j1 := eq21086 (σ x) (σ y)
       grind)
    | (have r₁ := eq1958
       have r₂ := eq21086 x y
       grind)
    | (have r₁ := eq1958
       have r₂ := eq21086 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1958
       have r₂ := eq21086 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1958 eq21086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq21086
  have eq32340 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq32339
  have eq78132 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32340
       grind)
    | exact superpose eq32340 eq16
    | exact resolve eq16 eq32340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32340
  have eq78133 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq78132
       have r₂ := eq22 x
       grind)
    | exact resolve eq78132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78132
  have eq78156 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq279 y x
       have i₂ := eq78133
       grind)
    | exact superpose eq78133 eq279
    | exact resolve eq279 eq78133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78133
  have eq78258 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq279 (σ y) (σ x)
       have i₂ := eq78156
       grind)
    | exact superpose eq78156 eq279
    | exact resolve eq279 eq78156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78156
  have eq78314 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78258
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq78258
    | exact resolve eq78258 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78258
  have eq78355 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq78314
       grind)
    | exact superpose eq78314 eq10
    | exact resolve eq10 eq78314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78314
  have eq78466 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78355
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78355
    | exact resolve eq78355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78355
  have eq78468 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78466
       grind)
    | exact superpose eq78466 eq16
    | exact resolve eq16 eq78466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78466
  have eq78469 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq78468
       have r₂ := eq22 x
       grind)
    | exact resolve eq78468 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq78468
  have eq78515 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq78469
       grind)
    | exact superpose eq78469 eq10
    | exact resolve eq10 eq78469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78469
  have eq78627 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78515
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq78515
    | exact resolve eq78515 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78515
  have eq78628 : y = (M.op y y) := by grind
  clear eq78627
  have eq78685 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq247 y X0
       have i₂ := eq78628
       grind)
    | exact superpose eq78628 eq247
    | exact resolve eq247 eq78628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq78820 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq78628
       grind)
    | exact superpose eq78628 eq9
    | exact resolve eq9 eq78628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78841 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq304 y y x
       have i₂ := eq78628
       grind)
    | exact superpose eq78628 eq304
    | exact resolve eq304 eq78628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78628
  have eq78885 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq78841 X0
       have i₂ := eq279 y X0
       grind)
    | exact superpose eq279 eq78841
    | exact resolve eq78841 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq78841
  have eq79117 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78820 X0
       have i₂ := eq78885 X0
       grind)
    | exact superpose eq78885 eq78820
    | exact resolve eq78820 eq78885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79194 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) y) X1) = (M.op (M.op (M.op (M.op (M.op y X0) y) X1) X0) (M.op (M.op (M.op y X0) y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq304 (M.op (M.op y X0) y) X1 X0
       have i₂ := eq78820 X0
       grind)
    | exact superpose eq78820 eq304
    | exact resolve eq304 eq78820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq78820
  have eq79250 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79194 X0 X1
       have i₂ := eq78885 X0
       grind)
    | exact superpose eq78885 eq79194
    | exact resolve eq79194 eq78885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79194
  have eq79291 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79250 X0 X0
       have i₂ := eq79117 X0
       grind)
    | exact superpose eq79117 eq79250
    | exact resolve eq79250 eq79117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79250
  have eq79316 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq78885 X0
       have i₂ := eq79117 X0
       grind)
    | exact superpose eq79117 eq78885
    | exact resolve eq78885 eq79117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78885 eq79117
  have eq81564 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq79291 X0 (M.op (M.op (σ y) X0) (σ y))
       have i₂ := eq78685 X0
       grind)
    | exact superpose eq78685 eq79291
    | exact resolve eq79291 eq78685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78685
  have eq81571 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq81564 X0
       have i₂ := eq79291 X0 (σ y)
       grind)
    | exact superpose eq79291 eq81564
    | exact resolve eq81564 eq79291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79291 eq81564
  have eq82999 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81571 (σ x)
       grind)
    | exact superpose eq81571 eq16
    | exact resolve eq16 eq81571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81571
  have eq83104 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq82999
       have i₂ := eq79316 x
       grind)
    | exact superpose eq79316 eq82999
    | exact resolve eq82999 eq79316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79316 eq82999
  have eq83105 : False := by grind
  exact eq83105

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq189 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
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
  have eq207 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq211 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq207 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq207
    | exact resolve eq207 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq207 X0
       grind)
    | exact superpose eq207 eq9
    | exact resolve eq9 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq247 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq211 X0
       grind)
    | exact superpose eq211 eq9
    | exact resolve eq9 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq279 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq217
    | exact resolve eq217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq304 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq279 X0 X1
       grind)
    | exact superpose eq279 eq9
    | exact resolve eq9 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq187 x y
       grind)
    | exact superpose eq187 eq16
    | (have j1 := eq187 x y
       grind)
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq21044 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq189 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq189
    | exact resolve eq189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq21165 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21044 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq21044
    | (have j0 := eq21044 X0 X1
       grind)
    | exact resolve eq21044 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21044
  have eq32363 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1958
       have i₂ := eq21165 x y
       grind)
    | exact superpose eq21165 eq1958
    | (have j1 := eq21165 (σ x) (σ y)
       grind)
    | (have r₁ := eq1958
       have r₂ := eq21165 x y
       grind)
    | (have r₁ := eq1958
       have r₂ := eq21165 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1958
       have r₂ := eq21165 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1958 eq21165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq21165
  have eq32364 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq32363
  have eq74226 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32364
       grind)
    | exact superpose eq32364 eq16
    | exact resolve eq16 eq32364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32364
  have eq74227 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq74226
       have r₂ := eq22 x
       grind)
    | exact resolve eq74226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74226
  have eq74250 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq279 y x
       have i₂ := eq74227
       grind)
    | exact superpose eq74227 eq279
    | exact resolve eq279 eq74227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74227
  have eq74349 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq279 (σ y) (σ x)
       have i₂ := eq74250
       grind)
    | exact superpose eq74250 eq279
    | exact resolve eq279 eq74250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74250
  have eq74402 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74349
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq74349
    | exact resolve eq74349 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74349
  have eq74443 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq74402
       grind)
    | exact superpose eq74402 eq10
    | exact resolve eq10 eq74402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74402
  have eq74554 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74443
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq74443
    | exact resolve eq74443 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74443
  have eq74556 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74554
       grind)
    | exact superpose eq74554 eq16
    | exact resolve eq16 eq74554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74554
  have eq74557 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq74556
       have r₂ := eq22 x
       grind)
    | exact resolve eq74556 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq74556
  have eq74603 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq74557
       grind)
    | exact superpose eq74557 eq10
    | exact resolve eq10 eq74557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74557
  have eq74715 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74603
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq74603
    | exact resolve eq74603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74603
  have eq74716 : y = (M.op y y) := by grind
  clear eq74715
  have eq74773 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq247 y X0
       have i₂ := eq74716
       grind)
    | exact superpose eq74716 eq247
    | exact resolve eq247 eq74716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq74908 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq74716
       grind)
    | exact superpose eq74716 eq9
    | exact resolve eq9 eq74716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74929 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq304 y y x
       have i₂ := eq74716
       grind)
    | exact superpose eq74716 eq304
    | exact resolve eq304 eq74716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74716
  have eq74970 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq74929 X0
       have i₂ := eq279 y X0
       grind)
    | exact superpose eq279 eq74929
    | exact resolve eq74929 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq74929
  have eq75686 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq74908 X0
       have i₂ := eq74970 X0
       grind)
    | exact superpose eq74970 eq74908
    | exact resolve eq74908 eq74970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75763 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) y) X1) = (M.op (M.op (M.op (M.op (M.op y X0) y) X1) X0) (M.op (M.op (M.op y X0) y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq304 (M.op (M.op y X0) y) X1 X0
       have i₂ := eq74908 X0
       grind)
    | exact superpose eq74908 eq304
    | exact resolve eq304 eq74908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq74908
  have eq75820 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75763 X0 X1
       have i₂ := eq74970 X0
       grind)
    | exact superpose eq74970 eq75763
    | exact resolve eq75763 eq74970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75763
  have eq75861 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75820 X0 X0
       have i₂ := eq75686 X0
       grind)
    | exact superpose eq75686 eq75820
    | exact resolve eq75820 eq75686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75820
  have eq75886 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq74970 X0
       have i₂ := eq75686 X0
       grind)
    | exact superpose eq75686 eq74970
    | exact resolve eq74970 eq75686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74970 eq75686
  have eq78134 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq75861 X0 (M.op (M.op (σ y) X0) (σ y))
       have i₂ := eq74773 X0
       grind)
    | exact superpose eq74773 eq75861
    | exact resolve eq75861 eq74773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74773
  have eq78141 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq78134 X0
       have i₂ := eq75861 X0 (σ y)
       grind)
    | exact superpose eq75861 eq78134
    | exact resolve eq78134 eq75861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75861 eq78134
  have eq79569 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78141 (σ x)
       grind)
    | exact superpose eq78141 eq16
    | exact resolve eq16 eq78141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78141
  have eq79674 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq79569
       have i₂ := eq75886 x
       grind)
    | exact superpose eq75886 eq79569
    | exact resolve eq79569 eq75886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75886 eq79569
  have eq79675 : False := by grind
  exact eq79675

/-- `Equation3748`: `x ◇ y = (y ◇ x) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxy_pyx_Equation3748 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3748 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3748.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq9 X0 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq171 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq187 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq171 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq171
    | (have j0 := eq171 X0
       grind)
    | exact resolve eq171 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq171
  have eq189 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq187
    | (have j0 := eq187 X0
       grind)
    | exact resolve eq187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq190 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq189 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq189 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq189 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq193 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq190 (σ X0)
       grind)
    | exact superpose eq190 eq15
    | exact resolve eq15 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (k X1 (k (τ (σ X0)) X0))) = (k (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X0 X1
       have i₂ := eq190 (σ X0)
       grind)
    | exact superpose eq190 eq24
    | exact resolve eq24 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq202 : ∀ X0 X1 : G, (σ (k X1 (k (τ (σ X0)) X0))) = (M.op (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1
       have i₂ := eq36 (σ X0) (σ X1)
       grind)
    | exact superpose eq36 eq197
    | exact resolve eq197 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq206 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq193 X0
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq193
    | exact resolve eq193 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq211 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq202
    | exact resolve eq202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq216 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq190 X0
       grind)
    | exact superpose eq190 eq211
    | exact resolve eq211 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq211
  have eq219 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq216
    | exact resolve eq216 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq216
  have eq220 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X0 X0))) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq206 X0
       grind)
    | exact superpose eq206 eq219
    | exact resolve eq219 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq249 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq16
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq257 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq249
       have i₂ := eq206 x
       grind)
    | exact superpose eq206 eq249
    | exact resolve eq249 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq389 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (M.op (σ (M.op X0 (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ (M.op X1 X1)) (σ X0)
       have i₂ := eq220 X1 X0
       grind)
    | exact superpose eq220 eq9
    | exact resolve eq9 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (M.op (σ (M.op X0 (M.op X1 X1))) (σ (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq206 (M.op X1 X1)
       grind)
    | exact superpose eq206 eq389
    | exact resolve eq389 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq411 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (σ (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq401 X0 X1
       have i₂ := eq220 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq220 eq401
    | exact resolve eq401 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq401
  have eq415 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (σ (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq411 X0 X1
       have i₂ := eq9 (M.op X1 X1) X0
       grind)
    | exact superpose eq9 eq411
    | exact resolve eq411 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq2700 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq257
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq257
    | (have j1 := eq14 (σ x) (σ (M.op x x))
       grind)
    | (have r₁ := eq257
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq257
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq257 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq2701 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq2700
  have eq24185 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2701
       grind)
    | exact superpose eq2701 eq16
    | exact resolve eq16 eq2701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701
  have eq24186 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24185
       have r₂ := eq206 x
       grind)
    | exact resolve eq24185 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24185
  have eq24188 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24186
       grind)
    | exact superpose eq24186 eq10
    | exact resolve eq10 eq24186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24186
  have eq24293 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24188
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24188
    | exact resolve eq24188 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24188
  have eq24323 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24293
       grind)
    | exact superpose eq24293 eq16
    | exact resolve eq16 eq24293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24293
  have eq24324 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24323
       have r₂ := eq206 x
       grind)
    | exact resolve eq24323 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq24323
  have eq24712 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq24324
       grind)
    | exact superpose eq24324 eq10
    | exact resolve eq10 eq24324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24324
  have eq24825 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24712
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24712
    | exact resolve eq24712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24712
  have eq24826 : x = (M.op x x) := by grind
  clear eq24825
  have eq24899 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq415 X0 x
       have i₂ := eq24826
       grind)
    | exact superpose eq24826 eq415
    | exact resolve eq415 eq24826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq24826
  have eq28963 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24899 y
       grind)
    | exact superpose eq24899 eq16
    | (have r₁ := eq16
       have r₂ := eq24899 y
       grind)
    | exact resolve eq16 eq24899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24899
  have eq29102 : False := by grind
  exact eq29102

/-- `Equation3794`: `x ◇ y = (z ◇ x) ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxx_pyx_pxy_Equation3794 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3794 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3794.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X0) (M.op X2 X1)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X3) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 X1) X3 (M.op X2 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) (M.op x y)) := by
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
  have eq178 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op (M.op X3 X0) X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X3 X1) (M.op X3 X0)
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq181
    | exact resolve eq181 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq183 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (M.op x X1)
       have i₂ := eq16 X1 X1 x
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq642 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : (M.op x y) = (k x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq642
       have i₂ := eq183
       grind)
    | exact superpose eq183 eq642
    | exact resolve eq642 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq663 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq663 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq663 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq663 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq663 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq671 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq211 X0 X0
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq211
    | exact resolve eq211 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq672 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq16
    | exact resolve eq16 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq16
    | exact resolve eq16 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : (M.op x y) = (M.op (k x x) (M.op x y)) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq664 x
       grind)
    | exact superpose eq664 eq177
    | exact resolve eq177 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : (M.op y x) = (M.op (M.op x y) (k x x)) := by
    first
    | (have i₁ := eq174 x
       have i₂ := eq664 x
       grind)
    | exact superpose eq664 eq174
    | exact resolve eq174 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : (k y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq183
       have i₂ := eq664 y
       grind)
    | exact superpose eq664 eq183
    | exact resolve eq183 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq686 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq178 sF2
       have i₂ := eq664 sF2
       grind)
    | exact superpose eq664 eq178
    | exact resolve eq178 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq175 sF2
       have i₂ := eq664 sF2
       grind)
    | exact superpose eq664 eq175
    | exact resolve eq175 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : (M.op (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq192
       have i₂ := eq664 sF4
       grind)
    | exact superpose eq664 eq192
    | exact resolve eq192 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq691
       have i₂ := eq664 sF3
       grind)
    | exact superpose eq664 eq691
    | exact resolve eq691 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq694 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq686
    | exact resolve eq686 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq698 : (k y y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq680
       have i₂ := eq664 sF0
       grind)
    | exact superpose eq664 eq680
    | exact resolve eq680 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq699 : (M.op x y) = (M.op (k x x) (M.op x y)) := by
    first
    | (have i₁ := eq678
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq678
    | exact resolve eq678 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq731 : (k (σ y) (σ y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq698
       grind)
    | exact superpose eq698 eq40
    | exact resolve eq40 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq731
    | exact resolve eq731 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq734 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq732
    | exact resolve eq732 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq736 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq734
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq734
    | exact resolve eq734 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq838 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq692 eq672
    | exact resolve eq672 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq1230 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq653
       grind)
    | exact superpose eq653 eq40
    | exact resolve eq40 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq653
  have eq1231 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1230
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1230
    | exact resolve eq1230 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1233 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq1231
    | exact resolve eq1231 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1235 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1233
       have i₂ := eq664 sF0
       grind)
    | exact superpose eq664 eq1233
    | exact resolve eq1233 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1235 eq646
    | exact resolve eq646 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq1235
  have eq1757 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq1750
       have r₂ := eq27
       grind)
    | exact resolve eq1750 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1761 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1757
       have i₂ := eq664 sF3
       grind)
    | exact superpose eq664 eq1757
    | exact resolve eq1757 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1763 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1761 eq115
    | exact resolve eq115 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1761
  have eq1785 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1763
       have i₂ := eq698
       grind)
    | exact superpose eq698 eq1763
    | exact resolve eq1763 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq1763
  have eq1788 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq29 eq1785
    | exact resolve eq1785 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1789 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1788
  have eq1802 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1789 eq41
    | exact resolve eq41 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1804 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1789 eq671
    | exact resolve eq671 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq1809 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq1802
    | exact resolve eq1802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq1811 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq736 eq1809
    | exact resolve eq1809 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq1809
  have eq1813 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1811
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1811
    | exact resolve eq1811 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq1826 : (M.op y x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq679
       have i₂ := eq1804
       grind)
    | exact superpose eq1804 eq679
    | exact resolve eq679 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq1827 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq699
       have i₂ := eq1804
       grind)
    | exact superpose eq1804 eq699
    | exact resolve eq699 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq1833 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1804
       grind)
    | exact superpose eq1804 eq39
    | exact resolve eq39 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1840 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1833
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1833
    | exact resolve eq1833 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1852 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1813 eq838
    | exact resolve eq838 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq1864 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1813 eq673
    | exact resolve eq673 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq2025 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X2) X4) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X3 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op (M.op X0 X3) X2) X4 (M.op X3 X1)
       have i₂ := eq176 X3 X1 X0 X2
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2026 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X4) X2)) = (M.op (M.op (M.op X4 X1) X3) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X3 (M.op (M.op X0 X4) X2) (M.op X4 X1)
       have i₂ := eq176 X4 X1 X0 X2
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2037 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X2) X4) = (M.op X2 (M.op (M.op X3 X0) X4)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2025 X0 x X2 X3 X4
       have i₂ := eq2026 X3 x X4 X2 X0
       grind)
    | exact superpose eq2026 eq2025
    | exact resolve eq2025 eq2026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025 eq2026
  have eq2110 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1827 eq174
    | exact resolve eq174 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2124 : (k (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2110
       have i₂ := eq664 sF0
       grind)
    | exact superpose eq664 eq2110
    | exact resolve eq2110 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110
  have eq2127 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1789 eq2124
    | exact resolve eq2124 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2131 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1840 eq694
    | exact resolve eq694 eq1840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2245 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op (M.op (M.op X1 x) X0) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1827 eq179
    | exact resolve eq179 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2296 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op X0 (M.op (M.op x X1) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2245 x X0
       have i₂ := eq2037 X0 x x sF0
       grind)
    | exact superpose eq2037 eq2245
    | exact resolve eq2245 eq2037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq2389 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op X0 (M.op X1 y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq177 eq2296
    | exact resolve eq2296 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2296
  have eq2511 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2131 eq175
    | exact resolve eq175 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2519 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op (M.op (M.op X1 (σ x)) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq2131 eq179
    | exact resolve eq179 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2527 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op X0 (M.op (M.op (σ x) X1) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2519 x X0
       have i₂ := eq2037 X0 x sF2 sF4
       grind)
    | exact superpose eq2037 eq2519
    | exact resolve eq2519 eq2037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037 eq2519
  have eq2531 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq192 eq2511
    | exact resolve eq2511 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq2511
  have eq2534 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op X0 (M.op X1 (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq178 eq2527
    | exact resolve eq2527 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq2527
  have eq2536 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2531
       have i₂ := eq664 sF3
       grind)
    | exact superpose eq664 eq2531
    | exact resolve eq2531 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531
  have eq2539 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1813 eq2536
    | exact resolve eq2536 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq2536
  have eq2547 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2539 eq16
    | exact resolve eq16 eq2539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2566 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1864 eq2547
    | exact resolve eq2547 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864 eq2547
  have eq2677 : (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1826
       grind)
    | exact superpose eq1826 eq11
    | (have j0 := eq11 (k y x) (M.op (M.op x y) x)
       grind)
    | exact resolve eq11 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq2689 : (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq2677
  have eq2699 : y = (k x x) ∨ (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2689
       have i₂ := eq664 x
       grind)
    | exact superpose eq664 eq2689
    | exact resolve eq2689 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689
  have eq2707 : x = y ∨ (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1804 eq2699
    | exact resolve eq2699 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699
  have eq2708 : (k y x) = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2707
  have eq2829 : (M.op x (M.op x y)) = (M.op (k y x) (k (M.op x y) (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2708 eq672
    | exact resolve eq672 eq2708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq2708
  have eq2835 : (M.op x (M.op x y)) = (M.op (k y x) x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1789 eq2829
    | exact resolve eq2829 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq2829
  have eq2843 : (M.op x y) = (M.op (k y x) x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1827 eq2835
    | exact resolve eq2835 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827 eq2835
  have eq3070 : (M.op x y) = (k (k y x) x) ∨ x = (k y x) ∨ (k y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 (k y x) x
       have i₂ := eq2843
       grind)
    | exact superpose eq2843 eq11
    | (have j0 := eq11 (M.op x y) (k (k y x) x)
       grind)
    | exact resolve eq11 eq2843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3071 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) (M.op (k y x) X0)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 (k y x)
       have i₂ := eq2843
       grind)
    | exact superpose eq2843 eq16
    | exact resolve eq16 eq2843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843
  have eq3091 : (k x x) = (k y x) ∨ (M.op x y) = (k (k y x) x) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3070
       have i₂ := eq664 x
       grind)
    | exact superpose eq664 eq3070
    | exact resolve eq3070 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3070
  have eq3095 : x = (k y x) ∨ (M.op x y) = (k (k y x) x) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1804 eq3091
    | exact resolve eq3091 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804 eq3091
  have eq3096 : (M.op x y) = (k (k y x) x) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq3095
  have eq5051 : (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq687 eq1852
    | exact resolve eq1852 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687 eq1852
  have eq5116 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq694 eq5051
    | exact resolve eq5051 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq5051
  have eq5155 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5116
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq5116
    | (have j1 := eq11 (M.op (σ x) (σ y)) (M.op (k (σ y) (σ x)) (σ x))
       grind)
    | exact resolve eq5116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5116
  have eq5177 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq5155
  have eq5194 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5177
       have i₂ := eq664 sF2
       grind)
    | exact superpose eq664 eq5177
    | exact resolve eq5177 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5177
  have eq5206 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1840 eq5194
    | exact resolve eq5194 eq1840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5194
  have eq5207 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5206
  have eq5214 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5207 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (k (k (σ y) (σ x)) (σ x))
       grind)
    | exact resolve eq11 eq5207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5215 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) (M.op (k (σ y) (σ x)) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5207 eq16
    | exact resolve eq16 eq5207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq5238 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5214
       have i₂ := eq664 sF2
       grind)
    | exact superpose eq664 eq5214
    | exact resolve eq5214 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214
  have eq5245 : (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1840 eq5238
    | exact resolve eq5238 eq1840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840 eq5238
  have eq5246 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5245
  have eq16987 : (M.op x y) = (M.op (M.op x y) (M.op (k y x) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3071 eq2389
    | exact resolve eq2389 eq3071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389 eq3071
  have eq17014 : (M.op x y) = (M.op (M.op x y) (M.op (k y x) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16987
  have eq17051 : (M.op x y) = (M.op (M.op x y) (M.op (k y x) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17014
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17014
    | exact resolve eq17014 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17014
  have eq17739 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5215 eq2534
    | exact resolve eq2534 eq5215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2534 eq5215
  have eq17756 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17739
  have eq17797 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2131 eq17756
    | exact resolve eq17756 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131 eq17756
  have eq17860 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17797 eq2566
    | exact resolve eq2566 eq17797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566 eq17797
  have eq17881 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (k (σ y) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17860
  have eq26413 : (σ (M.op x y)) = (k (σ (k y x)) (σ x)) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 (k y x)
       have i₂ := eq3096
       grind)
    | exact superpose eq3096 eq39
    | exact resolve eq39 eq3096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3096
  have eq26421 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (σ x)) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26413
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq26413
    | exact resolve eq26413 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26413
  have eq26422 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (σ x)) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26421
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26421
    | exact resolve eq26421 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26421
  have eq26423 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (σ x)) ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq26422
    | exact resolve eq26422 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26422
  have eq26844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26423 eq5246
    | exact resolve eq5246 eq26423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246 eq26423
  have eq26852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by grind
  clear eq26844
  have eq26857 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have r₁ := eq26852
       have r₂ := eq27
       grind)
    | exact resolve eq26852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26852
  have eq26878 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | exact superpose eq26857 eq107
    | exact resolve eq107 eq26857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq26857
  have eq26904 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq26878
    | exact resolve eq26878 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26878
  have eq26905 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26904
  have eq26934 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17051
       have i₂ := eq26905
       grind)
    | exact superpose eq26905 eq17051
    | exact resolve eq17051 eq26905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17051
  have eq26939 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq26905
       grind)
    | exact superpose eq26905 eq36
    | exact resolve eq36 eq26905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq26905
  have eq26953 : (M.op x y) = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26934
  have eq26969 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26939
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26939
    | exact resolve eq26939 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26939
  have eq26970 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq174 eq26953
    | exact resolve eq26953 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq26953
  have eq26995 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26969 eq17881
    | exact resolve eq17881 eq26969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17881 eq26969
  have eq27014 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26995
  have eq27028 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq27014
    | exact resolve eq27014 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27014
  have eq27040 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2539 eq27028
    | exact resolve eq27028 eq2539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2539 eq27028
  have eq27046 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27040 eq27
    | exact resolve eq27 eq27040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27040
  have eq27181 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26970 eq2127
    | exact resolve eq2127 eq26970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127 eq26970
  have eq27231 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq27181
  have eq27290 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27231 eq31
    | exact resolve eq31 eq27231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27231
  have eq27344 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq27290
    | exact resolve eq27290 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27290
  have eq27345 : x = (M.op x y) ∨ x = y := by grind
  clear eq27344
  have eq27352 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq27345
       grind)
    | exact superpose eq27345 eq22
    | exact resolve eq22 eq27345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27345
  have eq27536 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq27352
    | exact resolve eq27352 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27352
  have eq27618 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq27536 eq27046
    | (have r₁ := eq27046
       have r₂ := eq27536
       grind)
    | exact resolve eq27046 eq27536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27046 eq27536
  have eq27619 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27618
  have eq27620 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq27619
  have eq27669 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq27620 eq31
    | exact resolve eq31 eq27620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq27620
  have eq27729 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq27669
    | exact resolve eq27669 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27669
  have eq27730 : x = y := by grind
  clear eq27729
  have eq27748 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27730
       grind)
    | exact superpose eq27730 eq18
    | exact resolve eq18 eq27730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27749 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq27730
       grind)
    | exact superpose eq27730 eq24
    | exact resolve eq24 eq27730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq27730
  have eq27771 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27749
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27749
    | exact resolve eq27749 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27749
  have eq27772 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq27748
       have i₂ := eq664 x
       grind)
    | exact superpose eq664 eq27748
    | exact resolve eq27748 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27748
  have eq27778 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27771 eq26
    | exact resolve eq26 eq27771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq27771
  have eq27833 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq27778
       have i₂ := eq664 sF2
       grind)
    | exact superpose eq664 eq27778
    | exact resolve eq27778 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq27778
  have eq27851 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq27772
       grind)
    | exact superpose eq27772 eq39
    | exact resolve eq39 eq27772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq27772
  have eq27858 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq27851
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27851
    | exact resolve eq27851 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27851
  have eq27862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27833 eq27858
    | exact resolve eq27858 eq27833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27833 eq27858
  have eq27865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq27862
    | exact resolve eq27862 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq27862
  have eq27868 : False := by grind
  exact eq27868
