import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2340`: `x = (y ◇ (y ◇ (y ◇ y))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxx_pyx_Equation2340 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2340 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2340.models_iff G M).mp hM
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
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 (M.op X1 X1))) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (k X0 X1) (M.op X0 X0)
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (k X0 X1)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq186 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1029 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1030 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1030
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq1030
    | exact resolve eq1030 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1034 : (M.op x y) = (k y x) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1029
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1029
    | exact resolve eq1029 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1051 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1034
       grind)
    | exact superpose eq1034 eq40
    | exact resolve eq40 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1052 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1051
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1051
    | exact resolve eq1051 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1054 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq1052
    | exact resolve eq1052 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq1054 eq1033
    | exact resolve eq1033 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq1054
  have eq1064 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq1057
       have r₂ := eq27
       grind)
    | exact resolve eq1057 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1070 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq1064 eq142
    | exact resolve eq142 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1064
  have eq1075 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq30 eq1070
    | exact resolve eq1070 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1076 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1075
  have eq1083 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1076
       grind)
    | exact superpose eq1076 eq40
    | exact resolve eq40 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 : G, (M.op (M.op x (M.op x x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq186 x X0
       have i₂ := eq1076
       grind)
    | exact superpose eq1076 eq186
    | exact resolve eq186 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1087 : ∀ X0 : G, (M.op (M.op x (k x x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1085 X0
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1085
    | exact resolve eq1085 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1088 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1083
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1083
    | exact resolve eq1083 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1090 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1076 eq1087
    | exact resolve eq1087 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1091 : ∀ X0 : G, (M.op (k x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1090 X0
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1090
    | exact resolve eq1090 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1092 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1076 eq1091
    | exact resolve eq1091 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq1091
  have eq1097 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ x))) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1088 eq186
    | exact resolve eq186 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1099 : ∀ X0 : G, (M.op (M.op (σ x) (k (σ x) (σ x))) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1097 X0
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq1097
    | exact resolve eq1097 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1103 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1088 eq1099
    | exact resolve eq1099 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1104 : ∀ X0 : G, (M.op (k (σ x) (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1103 X0
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq1103
    | exact resolve eq1103 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1105 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1088 eq1104
    | exact resolve eq1104 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq1104
  have eq1109 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq1092 y
       grind)
    | exact superpose eq1092 eq18
    | (have j1 := eq1092 y
       grind)
    | exact resolve eq18 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1137 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1109 eq32
    | exact resolve eq32 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1174 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1137
    | exact resolve eq1137 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1175 : y = (M.op x y) ∨ x = y := by grind
  clear eq1174
  have eq1181 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq1175
       grind)
    | exact superpose eq1175 eq24
    | exact resolve eq24 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1183 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq1181
    | exact resolve eq1181 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181
  have eq1226 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1105 eq26
    | (have j1 := eq1105 (σ y)
       grind)
    | exact resolve eq26 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1255 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1226 eq27
    | exact resolve eq27 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1256 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1255
       have r₂ := eq1183
       grind)
    | exact resolve eq1255 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq1255
  have eq1258 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1256 eq32
    | exact resolve eq32 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1256
  have eq1296 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1258
    | exact resolve eq1258 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1258
  have eq1297 : x = y := by grind
  clear eq1296
  have eq1318 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1297
       grind)
    | exact superpose eq1297 eq18
    | exact resolve eq18 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1319 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1297
       grind)
    | exact superpose eq1297 eq24
    | exact resolve eq24 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1297
  have eq1324 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1319
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1319
    | exact resolve eq1319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1325 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1318
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1318
    | exact resolve eq1318 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1326 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1324 eq26
    | exact resolve eq26 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1324
  have eq1364 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1326
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq1326
    | exact resolve eq1326 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1326
  have eq1368 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq40
    | exact resolve eq40 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1325
  have eq1371 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1368
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1368
    | exact resolve eq1368 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1368
  have eq1373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1364 eq1371
    | exact resolve eq1371 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364 eq1371
  have eq1375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1373
    | exact resolve eq1373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1373
  have eq1377 : False := by grind
  exact eq1377

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq73 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq733 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq59669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq59669
    | exact resolve eq59669 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59669
  have eq59687 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq59676
       have r₂ := eq28
       grind)
    | exact resolve eq59676 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59676
  have eq59689 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq59687
    | exact resolve eq59687 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59687
  have eq59696 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq59689
  have eq59806 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq59696
    | exact resolve eq59696 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59696
  have eq59820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59806 eq113
    | exact resolve eq113 eq59806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59806
  have eq59834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq59820
  have eq59836 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq59834
       have r₂ := eq28
       grind)
    | exact resolve eq59834 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59834
  have eq59959 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq59836
  have eq60068 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59959
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59959
    | exact resolve eq59959 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59959
  have eq60075 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq60068
       grind)
    | exact superpose eq60068 eq45
    | exact resolve eq45 eq60068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60068
  have eq60101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq60075
    | exact resolve eq60075 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60075
  have eq60539 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq60101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq60539
    | exact resolve eq60539 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60539
  have eq60559 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq60548
       have r₂ := eq28
       grind)
    | exact resolve eq60548 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60548
  have eq60561 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq60559
    | exact resolve eq60559 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60559
  have eq60562 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq60561
  have eq60570 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq60562
  have eq60680 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq60570
    | exact resolve eq60570 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60570
  have eq60817 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60680 eq60101
    | exact resolve eq60101 eq60680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60101 eq60680
  have eq60825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60817
  have eq60829 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq60825
       have r₂ := eq28
       grind)
    | exact resolve eq60825 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60825
  have eq60831 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60829 eq28
    | exact resolve eq28 eq60829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60833 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60829 eq74
    | (have r₁ := eq74
       have r₂ := eq60829
       grind)
    | exact resolve eq74 eq60829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq60829
  have eq60901 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq60833
  have eq124120 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60901 eq113
    | exact resolve eq113 eq60901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124142 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq124120
  have eq124156 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq124142
       have r₂ := eq60831
       grind)
    | exact resolve eq124142 eq60831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124142
  have eq124184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq124156
  have eq124334 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq124184
    | exact resolve eq124184 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124184
  have eq125383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq124334 eq113
    | exact resolve eq113 eq124334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq124334
  have eq125401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq125383
  have eq125405 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq125401
       have r₂ := eq28
       grind)
    | exact resolve eq125401 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125401
  have eq125414 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq125405
  have eq125547 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq125414
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq125414
    | exact resolve eq125414 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125414
  have eq126436 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq125547
       grind)
    | exact superpose eq125547 eq45
    | exact resolve eq45 eq125547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125547
  have eq126466 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq126436
    | exact resolve eq126436 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126436
  have eq126685 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126466 eq60901
    | exact resolve eq60901 eq126466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60901
  have eq126695 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq126685
  have eq126703 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq126695
       have r₂ := eq60831
       grind)
    | exact resolve eq126695 eq60831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60831 eq126695
  have eq126741 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq126703
  have eq126891 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq126741
    | exact resolve eq126741 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126741
  have eq126923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126891 eq126466
    | exact resolve eq126466 eq126891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126466 eq126891
  have eq126931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq126923
  have eq126939 : y = (M.op x y) := by
    first
    | (have r₁ := eq126931
       have r₂ := eq28
       grind)
    | exact resolve eq126931 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126931
  have eq126941 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq126939 eq21
    | exact resolve eq21 eq126939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq126947 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq126939 eq73
    | (have r₁ := eq73
       have r₂ := eq126939
       grind)
    | exact resolve eq73 eq126939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq127102 : y = (k x y) ∨ x = (M.op y y) := by grind
  clear eq126947
  have eq127174 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq126941
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq126941
    | exact resolve eq126941 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126941
  have eq127187 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq127174 eq27
    | exact resolve eq27 eq127174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq151745 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq127102
       grind)
    | exact superpose eq127102 eq45
    | exact resolve eq45 eq127102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151762 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq733 x y
       have i₂ := eq127102
       grind)
    | exact superpose eq127102 eq733
    | (have j0 := eq733 x y
       grind)
    | exact resolve eq733 eq127102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127102
  have eq151763 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq151762
  have eq151770 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq151763
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq151763
    | exact resolve eq151763 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151763
  have eq151785 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq127174 eq151745
    | exact resolve eq151745 eq127174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151745
  have eq151787 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq127174 eq151770
    | exact resolve eq151770 eq127174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151770
  have eq151801 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq151785
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq151785
    | exact resolve eq151785 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151785
  have eq151802 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq151787
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq151787
    | exact resolve eq151787 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151787
  have eq151814 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq127174 eq151801
    | exact resolve eq151801 eq127174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151801
  have eq151815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq127187 eq151802
    | exact resolve eq151802 eq127187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151802
  have eq151821 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq151815
       have r₂ := eq28
       grind)
    | exact resolve eq151815 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151815
  have eq151827 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq151821
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq151821
    | exact resolve eq151821 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151821
  have eq151833 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq127174 eq151827
    | exact resolve eq151827 eq127174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151827
  have eq151839 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq151833
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq151833
    | exact resolve eq151833 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151833
  have eq151915 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq151839
  have eq152078 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq127187 eq151915
    | exact resolve eq151915 eq127187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151915
  have eq152119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq152078 eq151814
    | exact resolve eq151814 eq152078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151814 eq152078
  have eq152127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq152119
  have eq152129 : x = (M.op y y) := by
    first
    | (have r₁ := eq152127
       have r₂ := eq28
       grind)
    | exact resolve eq152127 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152127
  have eq152160 : (M.op x y) = (k x y) := by grind
  clear eq152129
  have eq152338 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq152160
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq152160
    | exact resolve eq152160 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq152160
  have eq152394 : y = (k x y) := by
    first
    | exact superpose eq126939 eq152338
    | exact resolve eq152338 eq126939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126939 eq152338
  have eq152829 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq152394
       grind)
    | exact superpose eq152394 eq45
    | exact resolve eq45 eq152394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq152846 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq733 x y
       have i₂ := eq152394
       grind)
    | exact superpose eq152394 eq733
    | (have j0 := eq733 x y
       grind)
    | exact resolve eq733 eq152394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq152394
  have eq152847 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq152846
  have eq152854 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq152847
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq152847
    | exact resolve eq152847 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152847
  have eq152868 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq127174 eq152829
    | exact resolve eq152829 eq127174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152829
  have eq152869 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq127174 eq152854
    | exact resolve eq152854 eq127174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152854
  have eq152883 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq152868
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq152868
    | exact resolve eq152868 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152868
  have eq152884 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq152869
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq152869
    | exact resolve eq152869 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152869
  have eq152896 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq127174 eq152883
    | exact resolve eq152883 eq127174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152883
  have eq152897 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq127187 eq152884
    | exact resolve eq152884 eq127187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152884
  have eq152903 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq152897
       have r₂ := eq28
       grind)
    | exact resolve eq152897 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152897
  have eq152909 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq152903
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq152903
    | exact resolve eq152903 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq152903
  have eq152915 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq127174 eq152909
    | exact resolve eq152909 eq127174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127174 eq152909
  have eq152921 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq152915
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq152915
    | exact resolve eq152915 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq152915
  have eq154132 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq152921
  have eq154297 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq127187 eq154132
    | exact resolve eq154132 eq127187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127187 eq154132
  have eq154349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq152896 eq154297
    | exact resolve eq154297 eq152896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152896 eq154297
  have eq154382 : False := by grind
  exact eq154382

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pyy_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq91 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq105 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq105 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq106 (σ X0)
       grind)
    | exact superpose eq106 eq10
    | exact resolve eq10 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq49
    | exact resolve eq49 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq112 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq111
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq111
    | exact resolve eq111 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq108
    | exact resolve eq108 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq108
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
  have eq247 : x = (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq441 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X1 X3))) = (M.op (M.op X4 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 X4 (M.op X1 (M.op X2 (M.op X0 X2))) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op X3 X4))) = (M.op (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1)))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X3 X5 (M.op X3 (M.op X0 X2)) X4
       have i₂ := eq52 X2 X3 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op y X0))) = (M.op (M.op X1 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y X1 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y X1 x X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X1 X2)
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X3 X2)) X1)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op X2 (M.op X3 X2)) X0 X2
       have i₂ := eq52 (M.op X2 (M.op X3 X2)) (M.op X2 (M.op X3 X2)) X0 X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X3 (M.op X4 X3)) X4 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq53 X4 X1 X0 X3
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1055 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq452
    | exact resolve eq452 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1077 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq1055 eq452
    | exact resolve eq452 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq1077 eq14
    | exact resolve eq14 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1125 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op X1 X0) X1) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1055 eq457
    | exact resolve eq457 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1130 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq457 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq457
    | (have j0 := eq457 X0 x y
       grind)
    | exact resolve eq457 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1141 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X1)) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq457 (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X1) X2 X3
       have i₂ := eq457 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq457 eq457
    | exact resolve eq457 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148 : (M.op y (M.op x y)) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq247 eq457
    | exact resolve eq457 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq457
  have eq1238 : ∀ X0 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq452 X0 y X0
       have i₂ := eq1108 X0
       grind)
    | (have i₁ := eq452 x y x
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq452
    | exact resolve eq452 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq8411 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X2 (M.op X0 (M.op X1 (M.op X2 X1)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq515 X3 X2 X2 X0
       have i₂ := eq52 X2 X2 X0 X1
       grind)
    | exact superpose eq52 eq515
    | exact resolve eq515 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq515
  have eq9637 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq433 (M.op X1 (M.op x X1)) sF4 sF3
       have i₂ := eq53 sF3 X1 x sF4
       grind)
    | exact superpose eq53 eq433
    | exact resolve eq433 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq25031 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X6 (M.op X4 (M.op X1 X4))) X6) = (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq441 (M.op X4 (M.op X1 X4)) (M.op X2 (M.op X0 X2)) x X5 X6
       have i₂ := eq520 X0 X2 x X4 X1
       grind)
    | exact superpose eq520 eq441
    | exact resolve eq441 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq520
  have eq25180 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) = X1 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq25031 X0 X1 X2 x X5 x
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq25031
    | exact resolve eq25031 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25031
  have eq32121 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op X2 y) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq442 (M.op X2 y) y X2 X1 X3 x
       have i₂ := eq445 (M.op X2 y) X0
       grind)
    | exact superpose eq445 eq442
    | exact resolve eq442 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq445
  have eq32609 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq32121 X0 X1 x X3
       have i₂ := eq1108 x
       grind)
    | (have i₁ := eq32121 X0 X1 x X3
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq32121
    | (have j0 := eq32121 X0 X1 x X3
       grind)
    | exact resolve eq32121 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq32121
  have eq32936 : ∀ X1 X3 : G, y = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq1130 eq32609
    | exact resolve eq32609 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq32609
  have eq85007 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X1 X0) X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9637 (M.op (M.op sF4 sF2) (M.op (M.op X1 x) X1)) (M.op sF4 sF2)
       have i₂ := eq458 (M.op sF4 sF2) X1 x (M.op sF4 sF2)
       grind)
    | exact superpose eq458 eq9637
    | exact resolve eq9637 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq107895 : ∀ X0 X2 : G, (M.op (M.op x y) x) = (M.op X0 (M.op y (M.op X2 (M.op X0 X2)))) := by
    intro X0 X2
    first
    | exact superpose eq32936 eq53
    | exact resolve eq53 eq32936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq32936
  have eq152418 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X0 X1) (σ y))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq9637 eq1141
    | exact resolve eq1141 eq9637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq9637
  have eq419173 : ∀ X0 X1 : G, y = (M.op (M.op y x) (M.op X0 (M.op (M.op X1 (M.op y X1)) X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq25180 y y X1 X0
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq25180
    | exact resolve eq25180 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq419229 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq419173 x x
       have i₂ := eq25180 y x x x
       grind)
    | exact superpose eq25180 eq419173
    | exact resolve eq419173 eq25180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25180 eq419173
  have eq448473 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq419229 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq419229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419229
  have eq448480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq448473
    | exact resolve eq448473 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448473
  have eq448491 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq448480
       have r₂ := eq27
       grind)
    | exact resolve eq448480 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448480
  have eq448750 : (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (σ x)) (σ y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq448491 eq152418
    | exact resolve eq152418 eq448491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152418 eq448491
  have eq448755 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq85007 eq448750
    | exact resolve eq448750 eq85007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85007 eq448750
  have eq451410 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq448755 eq112
    | exact resolve eq112 eq448755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448755
  have eq451830 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq451410
    | exact resolve eq451410 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451410
  have eq451831 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq451830
  have eq451964 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq451831
       grind)
    | exact superpose eq451831 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq451831
       grind)
    | exact resolve eq13 eq451831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451967 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq602 x X0
       have i₂ := eq451831
       grind)
    | exact superpose eq451831 eq602
    | (have j0 := eq602 x X0
       grind)
    | exact resolve eq602 eq451831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq452065 : x = (M.op (M.op x x) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1125 x x
       have i₂ := eq451831
       grind)
    | exact superpose eq451831 eq1125
    | exact resolve eq1125 eq451831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq451831
  have eq452189 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq451967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451967
  have eq452190 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq451964 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451964
  have eq452236 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1148 eq452065
    | exact resolve eq452065 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq452065
  have eq452302 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq452189 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq452189
    | (have j0 := eq452189 X0
       grind)
    | exact resolve eq452189 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452189
  have eq452689 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op y (M.op X0 (M.op (M.op x y) x))))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq452236 eq8411
    | exact resolve eq8411 eq452236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8411
  have eq452759 : (M.op (M.op x y) x) = (M.op y (M.op y (M.op (M.op x y) x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq452236 eq107895
    | exact resolve eq107895 eq452236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107895 eq452236
  have eq452777 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1238 eq452759
    | exact resolve eq452759 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452759
  have eq452832 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1238 eq452689
    | exact resolve eq452689 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq452689
  have eq472208 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq452190 sF0
       grind)
    | exact superpose eq452190 eq129
    | exact resolve eq129 eq452190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq452190
  have eq821549 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq452777 eq472208
    | exact resolve eq472208 eq452777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452777 eq472208
  have eq821627 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq821549
  have eq821634 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq821627
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq821627
    | exact resolve eq821627 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821627
  have eq821646 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq821634 eq452302
    | exact resolve eq452302 eq821634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452302 eq821634
  have eq821654 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq821646
  have eq824896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq821654 eq452832
    | exact resolve eq452832 eq821654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452832 eq821654
  have eq824899 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq824896
  have eq824903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq824899
    | exact resolve eq824899 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824899
  have eq825147 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq824903
       have r₂ := eq27
       grind)
    | exact resolve eq824903 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824903
  have eq825227 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq825147 eq29
    | exact resolve eq29 eq825147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq825147
  have eq825614 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq825227
    | exact resolve eq825227 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq825227
  have eq825615 : x = y := by grind
  clear eq825614
  have eq825646 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq825615
       grind)
    | exact superpose eq825615 eq18
    | exact resolve eq18 eq825615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq825647 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq825615
       grind)
    | exact superpose eq825615 eq24
    | exact resolve eq24 eq825615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq825615
  have eq826047 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq825647
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq825647
    | exact resolve eq825647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq825647
  have eq829804 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq826047 eq26
    | exact resolve eq26 eq826047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq826047
  have eq831233 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq829804 eq112
    | exact resolve eq112 eq829804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq829804
  have eq831927 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq831233
       have i₂ := eq825646
       grind)
    | exact superpose eq825646 eq831233
    | exact resolve eq831233 eq825646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825646 eq831233
  have eq832173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq831927 eq15
    | exact resolve eq15 eq831927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831927
  have eq832259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq832173
    | exact resolve eq832173 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq832173
  have eq832280 : False := by grind
  exact eq832280

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pyy_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
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
  clear eq44
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq97 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq106 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq106 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq111 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq107 y
       grind)
    | exact superpose eq107 eq70
    | exact resolve eq70 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq112 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq107 sF2
       grind)
    | exact superpose eq107 eq49
    | exact resolve eq49 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq113 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq112
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq112
    | exact resolve eq112 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq107 sF3
       grind)
    | exact superpose eq107 eq111
    | exact resolve eq111 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq120 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq97
       have i₂ := eq107 sF3
       grind)
    | exact superpose eq107 eq97
    | exact resolve eq97 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq121 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq120
       have i₂ := eq107 y
       grind)
    | exact superpose eq107 eq120
    | exact resolve eq120 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq120
  have eq130 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq432 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op y (M.op x y))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op X3 X4))) = (M.op (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1)))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X3 X5 (M.op X3 (M.op X0 X2)) X4
       have i₂ := eq52 X2 X3 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op y X0))) = (M.op (M.op X1 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y X1 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y X1 x X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = (M.op (M.op X1 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ y) X1 (σ x) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 (M.op (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op X1 X4))) X2))) = (M.op (M.op X5 X0) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op X1 X4))) X5 X1 X2
       have i₂ := eq53 X1 X3 X0 X4
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1054 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq452 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq452
    | exact resolve eq452 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq452
    | exact resolve eq452 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1057 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq452
    | exact resolve eq452 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1078 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq1056 eq452
    | exact resolve eq452 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1091 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1057 eq452
    | exact resolve eq452 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1109 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq1078 eq14
    | exact resolve eq14 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1131 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq457 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq457
    | (have j0 := eq457 X0 x y
       grind)
    | exact resolve eq457 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq457
    | (have j0 := eq457 X0 (σ x) (σ y)
       grind)
    | exact resolve eq457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq1221 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1091 eq14
    | exact resolve eq14 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1493 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1054 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1054
    | (have j0 := eq1054 y X0 x
       grind)
    | exact resolve eq1054 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9278 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq432 (M.op X1 (M.op x X1)) sF0 y
       have i₂ := eq53 y X1 x sF0
       grind)
    | exact superpose eq53 eq432
    | exact resolve eq432 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq432
  have eq32122 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op X2 y) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq442 (M.op X2 y) y X2 X1 X3 x
       have i₂ := eq445 (M.op X2 y) X0
       grind)
    | exact superpose eq445 eq442
    | exact resolve eq442 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq32125 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op X2 (σ y)) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq446 eq442
    | exact resolve eq442 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq446
  have eq32607 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq1221 eq32125
    | (have j0 := eq32125 X0 X1 (σ x) X3
       grind)
    | exact resolve eq32125 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq32125
  have eq32610 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq32122 X0 X1 x X3
       have i₂ := eq1109 x
       grind)
    | (have i₁ := eq32122 X0 X1 x X3
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq32122
    | (have j0 := eq32122 X0 X1 x X3
       grind)
    | exact resolve eq32122 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq32122
  have eq32936 : ∀ X1 X3 : G, (σ y) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq1136 eq32607
    | exact resolve eq32607 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq32607
  have eq32937 : ∀ X1 X3 : G, y = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq1131 eq32610
    | exact resolve eq32610 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq32610
  have eq124728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq124735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq124728
    | exact resolve eq124728 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124728
  have eq124746 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq124735
       have r₂ := eq27
       grind)
    | exact resolve eq124735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124735
  have eq124750 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq124746
    | exact resolve eq124746 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124746
  have eq124899 : (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq124750 eq32936
    | exact resolve eq32936 eq124750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32936 eq124750
  have eq124904 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq124899
       have i₂ := eq1054 sF4 sF2 sF2
       grind)
    | exact superpose eq1054 eq124899
    | exact resolve eq124899 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124899
  have eq125010 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq124904 eq121
    | exact resolve eq121 eq124904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq124904
  have eq125178 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq125010
    | exact resolve eq125010 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125010
  have eq125179 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq125178
  have eq125346 : y = (M.op (M.op x (M.op (M.op x y) x)) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq32937 x x
       have i₂ := eq125179
       grind)
    | exact superpose eq125179 eq32937
    | exact resolve eq32937 eq125179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32937 eq125179
  have eq125350 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125346
       have i₂ := eq1054 sF0 x x
       grind)
    | exact superpose eq1054 eq125346
    | exact resolve eq125346 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq125346
  have eq125764 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq125350
       grind)
    | exact superpose eq125350 eq114
    | exact resolve eq114 eq125350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq125778 : x = (M.op (M.op y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1493 y
       have i₂ := eq125350
       grind)
    | exact superpose eq125350 eq1493
    | exact resolve eq1493 eq125350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq125781 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq125350
       grind)
    | exact superpose eq125350 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq125350
       grind)
    | exact resolve eq13 eq125350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125897 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq125781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125781
  have eq125933 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125764
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq125764
    | exact resolve eq125764 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125764
  have eq126276 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq125933 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq125933
       grind)
    | exact resolve eq13 eq125933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125933
  have eq126393 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq126276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126276
  have eq127161 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125778
       have i₂ := eq125350
       grind)
    | exact superpose eq125350 eq125778
    | exact resolve eq125778 eq125350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125350 eq125778
  have eq127293 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq127161
  have eq127482 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op (M.op x y) x)) X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq127293 eq521
    | exact resolve eq521 eq127293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq127548 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op X2 y) X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X2 X3
    first
    | exact superpose eq9278 eq127482
    | exact resolve eq127482 eq9278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9278 eq127482
  have eq127627 : ∀ X2 X3 : G, (M.op (M.op X3 X2) X3) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2 X3
    first
    | (have i₁ := eq127548 x X2 X3
       have i₂ := eq452 X2 y x
       grind)
    | exact superpose eq452 eq127548
    | exact resolve eq127548 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq127548
  have eq129959 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq125897 sF0
       grind)
    | exact superpose eq125897 eq130
    | exact resolve eq130 eq125897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq125897
  have eq219917 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq127293 eq129959
    | exact resolve eq129959 eq127293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127293 eq129959
  have eq219991 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq219917
  have eq219997 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq219991
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq219991
    | exact resolve eq219991 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219991
  have eq220009 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq219997 eq126393
    | exact resolve eq126393 eq219997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126393 eq219997
  have eq220017 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq220009
  have eq220192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq220017 eq127627
    | exact resolve eq127627 eq220017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127627 eq220017
  have eq220193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq220192
  have eq220195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq220193
    | exact resolve eq220193 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220193
  have eq220268 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq220195
       have r₂ := eq27
       grind)
    | exact resolve eq220195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220195
  have eq220277 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq220268 eq29
    | exact resolve eq29 eq220268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq220268
  have eq220516 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq220277
    | exact resolve eq220277 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq220277
  have eq220517 : x = y := by grind
  clear eq220516
  have eq220539 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq220517
       grind)
    | exact superpose eq220517 eq18
    | exact resolve eq18 eq220517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq220540 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq220517
       grind)
    | exact superpose eq220517 eq24
    | exact resolve eq24 eq220517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq220517
  have eq220780 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq220540
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq220540
    | exact resolve eq220540 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq220540
  have eq220813 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq220780 eq26
    | exact resolve eq26 eq220780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq220780
  have eq221590 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq220813 eq113
    | exact resolve eq113 eq220813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq220813
  have eq221929 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq221590
       have i₂ := eq220539
       grind)
    | exact superpose eq220539 eq221590
    | exact resolve eq221590 eq220539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220539 eq221590
  have eq222042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq221929 eq15
    | exact resolve eq15 eq221929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221929
  have eq222128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq222042
    | exact resolve eq222042 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq222042
  have eq222149 : False := by grind
  exact eq222149

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pxy_pyy_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq88
    | exact resolve eq88 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq103 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq103 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq103 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq103 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq43
    | exact resolve eq43 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq109 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq104 sF2
       grind)
    | exact superpose eq104 eq49
    | exact resolve eq49 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq110 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq109
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq109
    | exact resolve eq109 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq104 sF2
       grind)
    | exact superpose eq104 eq107
    | exact resolve eq107 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq107
  have eq128 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq246 : x = (M.op x (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op X4 (M.op X3 X4))) = (M.op (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1)))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X3 X5 (M.op X3 (M.op X0 X2)) X4
       have i₂ := eq52 X2 X3 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op y X0))) = (M.op (M.op X1 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y X1 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y X1 x X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 : G, x = (M.op y (M.op X0 (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X0))) X3) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 (M.op X4 (M.op X2 X4))
       have i₂ := eq52 X2 X0 X1 X4
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq509 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 (σ x)))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1045 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq453 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq453
    | exact resolve eq453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq453
    | exact resolve eq453 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1048 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq453
    | exact resolve eq453 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1072 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq1047 eq453
    | exact resolve eq453 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op X1 X0) X1) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1047 eq458
    | exact resolve eq458 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1094 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq458 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq458
    | (have j0 := eq458 X0 x y
       grind)
    | exact resolve eq458 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : (M.op y (M.op x y)) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq246 eq458
    | exact resolve eq458 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq458
  have eq1142 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1048 eq453
    | exact resolve eq453 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1200 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq1072 eq14
    | exact resolve eq14 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1221 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1142 eq14
    | exact resolve eq14 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1238 : ∀ X0 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq453 X0 y X0
       have i₂ := eq1200 X0
       grind)
    | (have i₁ := eq453 x y x
       have i₂ := eq1200 X0
       grind)
    | exact superpose eq1200 eq453
    | exact resolve eq453 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1328 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) = X0 := by
    intro X0
    first
    | exact superpose eq1221 eq453
    | exact resolve eq453 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1498 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1045 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1045
    | (have j0 := eq1045 y X0 x
       grind)
    | exact resolve eq1045 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1522 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1328 (M.op x (M.op sF2 x))
       have i₂ := eq1045 sF2 x sF4
       grind)
    | exact superpose eq1045 eq1328
    | exact resolve eq1328 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq1328
  have eq1611 : ∀ X0 : G, (M.op (M.op y X0) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq1498 eq453
    | exact resolve eq453 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq1498
  have eq2025 : x = (M.op y (M.op (M.op (σ x) (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1522 eq455
    | exact resolve eq455 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq2028 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1522 eq456
    | exact resolve eq456 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq1522
  have eq20520 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (M.op X1 X0)) (M.op (σ y) (M.op (σ x) (σ y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq509 eq461
    | exact resolve eq461 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq509
  have eq32483 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op X2 y) X2)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq443 (M.op X2 y) y X2 X1 X3 x
       have i₂ := eq446 (M.op X2 y) X0
       grind)
    | exact superpose eq446 eq443
    | exact resolve eq443 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq446
  have eq32973 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq32483 X0 X1 x X3
       have i₂ := eq1200 x
       grind)
    | (have i₁ := eq32483 X0 X1 x X3
       have i₂ := eq1200 X0
       grind)
    | exact superpose eq1200 eq32483
    | (have j0 := eq32483 X0 X1 x X3
       grind)
    | exact resolve eq32483 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200 eq32483
  have eq33306 : ∀ X1 X3 : G, y = (M.op (M.op X1 (M.op (M.op x y) x)) (M.op X3 (M.op X1 X3))) := by
    intro X1 X3
    first
    | exact superpose eq1094 eq32973
    | exact resolve eq32973 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq32973
  have eq129400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq129401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq129400
    | exact resolve eq129400 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129400
  have eq129412 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq129401
       have r₂ := eq27
       grind)
    | exact resolve eq129401 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129401
  have eq129416 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq129412
    | exact resolve eq129412 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129412
  have eq129554 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq129416 eq20520
    | exact resolve eq20520 eq129416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129416
  have eq129560 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2028 eq129554
    | exact resolve eq129554 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028 eq129554
  have eq129598 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq129560 eq110
    | exact resolve eq110 eq129560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129560
  have eq129830 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq129598
    | exact resolve eq129598 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129598
  have eq129831 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq129830
  have eq130009 : y = (M.op y (M.op (M.op (σ x) (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20520 y y
       have i₂ := eq129831
       grind)
    | exact superpose eq129831 eq20520
    | exact resolve eq20520 eq129831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20520 eq129831
  have eq130017 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2025 eq130009
    | exact resolve eq130009 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025 eq130009
  have eq130318 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq112
       have i₂ := eq130017
       grind)
    | exact superpose eq130017 eq112
    | exact resolve eq112 eq130017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq130347 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq130017
       grind)
    | exact superpose eq130017 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq130017
       grind)
    | exact resolve eq13 eq130017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130432 : x = (M.op (M.op x x) (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1088 x x
       have i₂ := eq130017
       grind)
    | exact superpose eq130017 eq1088
    | exact resolve eq1088 eq130017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq130017
  have eq130470 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq130347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130347
  have eq130481 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1110 eq130432
    | exact resolve eq130432 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq130432
  have eq130549 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq130318
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq130318
    | exact resolve eq130318 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130318
  have eq130933 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op x y) x))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq130481 eq53
    | exact resolve eq53 eq130481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq131044 : y = (M.op (M.op y (M.op (M.op x y) x)) (M.op (M.op x y) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq130481 eq33306
    | exact resolve eq33306 eq130481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33306 eq130481
  have eq131047 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1611 eq131044
    | exact resolve eq131044 eq1611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611 eq131044
  have eq131107 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1238 eq130933
    | exact resolve eq130933 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq130933
  have eq131200 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq130549 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq130549
       grind)
    | exact resolve eq13 eq130549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130549
  have eq131324 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq131200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131200
  have eq134091 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq128
       have i₂ := eq130470 sF0
       grind)
    | exact superpose eq130470 eq128
    | exact resolve eq128 eq130470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq130470
  have eq224812 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq131047 eq134091
    | exact resolve eq134091 eq131047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131047 eq134091
  have eq224907 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq224812
  have eq224915 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq224907
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq224907
    | exact resolve eq224907 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224907
  have eq224927 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq224915 eq131324
    | exact resolve eq131324 eq224915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131324 eq224915
  have eq224930 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq224927
  have eq225120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq224930 eq131107
    | exact resolve eq131107 eq224930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131107 eq224930
  have eq225123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq225120
  have eq225124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq225123
    | exact resolve eq225123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225123
  have eq225256 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq225124
       have r₂ := eq27
       grind)
    | exact resolve eq225124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225124
  have eq225285 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq225256 eq29
    | exact resolve eq29 eq225256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq225256
  have eq225523 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq225285
    | exact resolve eq225285 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq225285
  have eq225524 : x = y := by grind
  clear eq225523
  have eq225546 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq225524
       grind)
    | exact superpose eq225524 eq18
    | exact resolve eq18 eq225524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq225547 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq225524
       grind)
    | exact superpose eq225524 eq24
    | exact resolve eq24 eq225524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq225524
  have eq225788 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq225547
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq225547
    | exact resolve eq225547 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq225547
  have eq225821 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq225788 eq26
    | exact resolve eq26 eq225788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq225788
  have eq226621 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq225821 eq110
    | exact resolve eq110 eq225821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq225821
  have eq226974 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq226621
       have i₂ := eq225546
       grind)
    | exact superpose eq225546 eq226621
    | exact resolve eq226621 eq225546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225546 eq226621
  have eq227088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq226974 eq15
    | exact resolve eq15 eq226974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226974
  have eq227170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq227088
    | exact resolve eq227088 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq227088
  have eq227191 : False := by grind
  exact eq227191

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxy_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (M.op X0 X1) x X1 X2
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X1 X2)
       have i₂ := eq61 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X2 X0) X2)) X1) (M.op X3 X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq76 X3 (M.op (M.op X1 (M.op (M.op X2 X0) X2)) X1) X3
       have i₂ := eq80 X1 X2 X0 X3
       grind)
    | exact superpose eq80 eq76
    | exact resolve eq76 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1864 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1865 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1864 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1864 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1864 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq1876 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1865 (σ X0)
       grind)
    | exact superpose eq1865 eq15
    | exact resolve eq15 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1895 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1876 X0
       have i₂ := eq1865 X0
       grind)
    | exact superpose eq1865 eq1876
    | exact resolve eq1876 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865 eq1876
  have eq1931 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (σ X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (σ X0) X2 X1 (σ X0)
       have i₂ := eq1895 X0
       grind)
    | exact superpose eq1895 eq61
    | exact resolve eq61 eq1895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1935 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) (σ X0) X1
       have i₂ := eq1895 X0
       grind)
    | exact superpose eq1895 eq76
    | exact resolve eq76 eq1895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2849 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
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
  have eq2864 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2849 (σ X1) (σ X0)
       grind)
    | exact superpose eq2849 eq15
    | (have j1 := eq2849 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq2849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2887 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2864 X0 X1
       have i₂ := eq1895 X1
       grind)
    | exact superpose eq1895 eq2864
    | (have j0 := eq2864 X0 X1
       grind)
    | exact resolve eq2864 eq1895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq3769 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2887 X0 X1
       have i₂ := eq2849 X1 X0
       grind)
    | exact superpose eq2849 eq2887
    | (have j0 := eq2887 X0 X1
       have j1 := eq2849 X1 X0
       grind)
    | exact resolve eq2887 eq2849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2849 eq2887
  have eq82204 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X0) (M.op X1 (M.op (σ (M.op X0 X0)) X1))) ∨ (M.op (σ X2) (σ X0)) = (σ (M.op X2 X0)) ∨ (M.op X0 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 (σ X2) (σ X0) X1
       have i₂ := eq3769 X2 X0
       grind)
    | exact superpose eq3769 eq76
    | (have j1 := eq3769 X2 X0
       grind)
    | exact resolve eq76 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3769
  have eq82357 : ∀ X0 X2 : G, (M.op (σ X2) (σ X0)) = (σ (M.op X2 X0)) ∨ (σ X0) = (σ X2) ∨ (M.op X0 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq82204 X0 x X2
       have i₂ := eq1935 X0 x
       grind)
    | exact superpose eq1935 eq82204
    | (have j0 := eq82204 X0 x X2
       grind)
    | exact resolve eq82204 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935 eq82204
  have eq88062 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (σ X0) X1) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op X3 X1)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq936 X1 x (σ X0) X3
       have i₂ := eq1931 X0 (M.op (σ X0) X1) x
       grind)
    | exact superpose eq1931 eq936
    | exact resolve eq936 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq1931
  have eq1263210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82357 y x
       grind)
    | exact superpose eq82357 eq16
    | (have j1 := eq82357 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq82357 y x
       grind)
    | exact resolve eq16 eq82357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82357
  have eq1263819 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1263210
  have eq1264645 : ∀ X0 : G, y = (M.op (M.op (M.op (σ X0) y) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq88062 X0 y y
       have i₂ := eq1263819
       grind)
    | exact superpose eq1263819 eq88062
    | exact resolve eq88062 eq1263819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263819
  have eq1264660 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1264645 x
       have i₂ := eq88062 x y x
       grind)
    | (have i₁ := eq1264645 x
       have i₂ := eq88062 x x (M.op (M.op (M.op (σ x) y) (M.op (σ x) (σ (M.op x x)))) (M.op x y))
       grind)
    | exact superpose eq88062 eq1264645
    | exact resolve eq1264645 eq88062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88062 eq1264645
  have eq1264738 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1264660
       grind)
    | exact superpose eq1264660 eq10
    | exact resolve eq10 eq1264660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264660
  have eq1265021 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1264738
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1264738
    | exact resolve eq1264738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264738
  have eq1265022 : x = y := by grind
  clear eq1265021
  have eq1265025 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1265022
       grind)
    | exact superpose eq1265022 eq16
    | exact resolve eq16 eq1265022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265022
  have eq1265026 : False := by grind
  exact eq1265026

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq72 y x
       grind)
    | exact superpose eq72 eq69
    | (have j1 := eq72 y x
       grind)
    | exact resolve eq69 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
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
  have eq121 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq118
    | exact resolve eq118 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq118
  have eq452 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq102 eq72
    | (have j0 := eq72 (σ y) (σ x)
       grind)
    | exact resolve eq72 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq102
  have eq950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq949
    | exact resolve eq949 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq953 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq950
       have r₂ := eq27
       grind)
    | exact resolve eq950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq955 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq953
    | exact resolve eq953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq1244 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq955 eq452
    | exact resolve eq452 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1295 : (σ x) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq51 eq1244
    | exact resolve eq1244 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1244
  have eq1311 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1295
       have i₂ := eq14 sF3 sF2 sF4
       grind)
    | exact superpose eq14 eq1295
    | exact resolve eq1295 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1323 : ∀ X0 : G, x = (M.op (M.op (M.op X0 (M.op x y)) X0) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq452 X0 x x
       have i₂ := eq1311
       grind)
    | exact superpose eq1311 eq452
    | exact resolve eq452 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq1311
  have eq1397 : x = (M.op (M.op x (M.op (M.op x y) (M.op y (M.op x y)))) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq50 eq1323
    | exact resolve eq1323 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1323
  have eq1410 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1397
       have i₂ := eq14 y x sF0
       grind)
    | exact superpose eq14 eq1397
    | exact resolve eq1397 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1471 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1410 eq29
    | exact resolve eq29 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1410
  have eq1497 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq1471
    | exact resolve eq1471 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1471
  have eq1498 : x = y := by grind
  clear eq1497
  have eq1503 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1498
       grind)
    | exact superpose eq1498 eq18
    | exact resolve eq18 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1504 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1498
       grind)
    | exact superpose eq1498 eq24
    | exact resolve eq24 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1498
  have eq1532 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1504
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1504
    | exact resolve eq1504 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1504
  have eq1537 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1532 eq26
    | exact resolve eq26 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1532
  have eq1594 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1537 eq121
    | exact resolve eq121 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq1537
  have eq1610 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1594
       have i₂ := eq1503
       grind)
    | exact superpose eq1503 eq1594
    | exact resolve eq1594 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq1594
  have eq1614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1610 eq15
    | exact resolve eq15 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq1636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1614
    | exact resolve eq1614 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1614
  have eq1641 : False := by grind
  exact eq1641

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq10
    | exact resolve eq10 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq75
    | exact resolve eq75 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq75
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq126 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq478 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq578 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq631 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 x))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq974 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq578 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq578
    | exact resolve eq578 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq578
    | exact resolve eq578 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq997 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq976 eq578
    | exact resolve eq578 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq976
  have eq59384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq59385 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq59384
    | exact resolve eq59384 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59384
  have eq59395 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq59385
       have r₂ := eq28
       grind)
    | exact resolve eq59385 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59385
  have eq59398 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq59395 eq78
    | exact resolve eq78 eq59395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59395
  have eq59557 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq59398
    | exact resolve eq59398 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59398
  have eq59558 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59557
  have eq59582 : y = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq997 x
       have i₂ := eq59558
       grind)
    | exact superpose eq59558 eq997
    | exact resolve eq997 eq59558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq59584 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq59558
       grind)
    | exact superpose eq59558 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq59558
       grind)
    | exact resolve eq13 eq59558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59586 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq478 x X0
       have i₂ := eq59558
       grind)
    | exact superpose eq59558 eq478
    | (have j0 := eq478 x X0
       grind)
    | exact resolve eq478 eq59558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq59676 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59586 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59586
  have eq59677 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59584
  have eq59720 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq59676 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq59676
    | (have j0 := eq59676 X0
       grind)
    | exact resolve eq59676 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59676
  have eq60044 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59582
       have i₂ := eq59558
       grind)
    | exact superpose eq59558 eq59582
    | exact resolve eq59582 eq59558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59558 eq59582
  have eq60152 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq60044
  have eq60215 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y (M.op x y))) (M.op (M.op X0 (M.op X1 X0)) y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq60152 eq631
    | exact resolve eq631 eq60152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq60382 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq60215 X0 X1
       have i₂ := eq974 y sF0 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq974 eq60215
    | exact resolve eq60215 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq60215
  have eq61378 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq126
       have i₂ := eq59677 sF0
       grind)
    | exact superpose eq59677 eq126
    | exact resolve eq126 eq59677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq59677
  have eq99321 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq60152 eq61378
    | exact resolve eq61378 eq60152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60152 eq61378
  have eq99388 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq99321
  have eq99394 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq99388
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq99388
    | exact resolve eq99388 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99388
  have eq100003 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq99394 eq59720
    | exact resolve eq59720 eq99394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59720 eq99394
  have eq100010 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq100003
  have eq100134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq100010 eq60382
    | exact resolve eq60382 eq100010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60382 eq100010
  have eq100137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq100134
  have eq100138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq100137
    | exact resolve eq100137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100137
  have eq100226 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq100138
       have r₂ := eq28
       grind)
    | exact resolve eq100138 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100138
  have eq100241 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq100226 eq30
    | exact resolve eq30 eq100226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq100226
  have eq100431 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq100241
    | exact resolve eq100241 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq100241
  have eq100432 : x = y := by grind
  clear eq100431
  have eq100445 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq100432
       grind)
    | exact superpose eq100432 eq19
    | exact resolve eq19 eq100432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq100446 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq100432
       grind)
    | exact superpose eq100432 eq25
    | exact resolve eq25 eq100432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq100432
  have eq100651 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq100446
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq100446
    | exact resolve eq100446 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq100446
  have eq100675 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq100651 eq27
    | exact resolve eq27 eq100651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq100651
  have eq101218 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq100675 eq78
    | exact resolve eq78 eq100675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq100675
  have eq101434 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101218
       have i₂ := eq100445
       grind)
    | exact superpose eq100445 eq101218
    | exact resolve eq101218 eq100445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100445 eq101218
  have eq101489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq101434 eq15
    | exact resolve eq15 eq101434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101434
  have eq101565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq101489
    | exact resolve eq101489 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq101489
  have eq101586 : False := by grind
  exact eq101586
