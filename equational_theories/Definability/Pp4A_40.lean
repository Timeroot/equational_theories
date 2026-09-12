import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pxx_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) X0) x) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq118 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) := by
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
  have eq119 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq111 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq228 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129 eq51
    | exact resolve eq51 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq235 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq228 eq14
    | exact resolve eq14 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq458 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq119
    | (have r₁ := eq119
       have r₂ := eq129
       grind)
    | exact resolve eq119 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq129
  have eq459 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq458
  have eq1140 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq459 eq111
    | exact resolve eq111 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq1143 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1140
  have eq1151 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1143 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1143
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1143
       grind)
    | exact resolve eq13 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1159 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1151
  have eq1162 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1159
    | exact resolve eq1159 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1162 eq111
    | exact resolve eq111 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq1162
  have eq1210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1207
  have eq1214 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1210
       have r₂ := eq27
       grind)
    | exact resolve eq1210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1217 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1214 eq235
    | exact resolve eq235 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq1214
  have eq1252 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1217
  have eq1255 : x = (M.op x y) := by
    first
    | (have r₁ := eq1252
       have r₂ := eq131
       grind)
    | exact resolve eq1252 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq1252
  have eq1289 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1255 eq20
    | exact resolve eq20 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1294 : x ≠ x ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq1255 eq118
    | (have r₁ := eq118
       have r₂ := eq1255
       grind)
    | exact resolve eq118 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1298 : x = (M.op x x) := by
    first
    | exact superpose eq1255 eq220
    | exact resolve eq220 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq1299 : y = (M.op y x) ∨ (k x y) = (M.op x x) := by grind
  clear eq1294
  have eq1306 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1289
    | exact resolve eq1289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1307 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1306 eq26
    | exact resolve eq26 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1923 : y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1299
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq1299
    | exact resolve eq1299 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298 eq1299
  have eq1927 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1923
       grind)
    | exact superpose eq1923 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1923
       grind)
    | exact resolve eq13 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq1935 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq1927
  have eq1937 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1935
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1935
    | exact resolve eq1935 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1935
  have eq1940 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq1255 eq1937
    | exact resolve eq1937 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq1937
  have eq1941 : x = (k x y) := by grind
  clear eq1940
  have eq1945 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1941
       grind)
    | exact superpose eq1941 eq44
    | exact resolve eq44 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1941
  have eq1952 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1306 eq1945
    | exact resolve eq1945 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1954 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1952
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1952
    | exact resolve eq1952 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1952
  have eq1955 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1306 eq1954
    | exact resolve eq1954 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306 eq1954
  have eq1958 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1955 eq76
    | (have j0 := eq76 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq76 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1955
  have eq1959 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1958
  have eq1961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1307 eq1959
    | exact resolve eq1959 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307 eq1959
  have eq1964 : False := by grind
  exact eq1964

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = (M.op X2 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq44 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X0) = (M.op X2 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq50 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq110 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq308 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq309 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq314 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1
       have j1 := eq110 X0 X1
       grind)
    | (have r₁ := eq309 X0 X1
       have r₂ := eq110 X0 X1
       grind)
    | (have r₁ := eq309 X1 X1
       have r₂ := eq110 X1 X1
       grind)
    | exact resolve eq309 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq309
  have eq327 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq314 (σ X0) (σ X1)
       grind)
    | exact superpose eq314 eq15
    | exact resolve eq15 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq314 X0 X1
       grind)
    | exact superpose eq314 eq327
    | exact resolve eq327 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq327
  have eq334 : False := by grind
  exact eq334

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_x_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq276 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
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
  have eq286 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq287 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq392 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq287 X1 X0
       grind)
    | exact superpose eq287 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq287 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq287 X0 X1
       grind)
    | exact resolve eq13 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq287 (σ x) (σ y)
       grind)
    | exact superpose eq287 eq16
    | (have j1 := eq287 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq392 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq406 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq401
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq401
    | exact resolve eq401 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq407 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq405 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq405 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq405 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq421 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq407 X1 (τ X0)
       grind)
    | exact superpose eq407 eq18
    | (have j1 := eq407 X1 (τ X0)
       grind)
    | exact resolve eq18 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq438 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq421 X1 (τ X0)
       grind)
    | exact superpose eq421 eq17
    | (have j1 := eq421 X1 (τ X0)
       grind)
    | exact resolve eq17 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq421
  have eq1038 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1033 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1033
    | (have j0 := eq1033 X0 X1
       grind)
    | exact resolve eq1033 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq1053 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1038 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1038
    | (have j0 := eq1038 X0 X1
       grind)
    | exact resolve eq1038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1056 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1053 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1053
    | (have j0 := eq1053 X0 X1
       grind)
    | exact resolve eq1053 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1112 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1056 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1056
    | (have j0 := eq1056 X1 (σ X0)
       grind)
    | exact resolve eq1056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1516 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1112 X0 X0
       have i₂ := eq407 X0 (σ X0)
       grind)
    | exact superpose eq407 eq1112
    | (have j0 := eq1112 X0 X1
       have j1 := eq407 X1 (σ X0)
       grind)
    | exact resolve eq1112 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq1112
  have eq1557 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1516 X0 X1
       have j1 := eq438 X1 (σ X0)
       grind)
    | (have r₁ := eq1516 X0 X0
       have r₂ := eq438 X0 (σ X0)
       grind)
    | exact resolve eq1516 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq1516
  have eq1738 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1557 X1 (σ X0)
       grind)
    | exact superpose eq1557 eq28
    | (have j1 := eq1557 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1557
  have eq1749 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1738 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1738
    | (have j0 := eq1738 X0 X1
       grind)
    | exact resolve eq1738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1763 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1749 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1749
    | (have j0 := eq1749 X0 X1
       grind)
    | exact resolve eq1749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq1772 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1763 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1763
    | (have j0 := eq1763 X0 X1
       grind)
    | exact resolve eq1763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1861 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1772 y x
       grind)
    | exact superpose eq1772 eq16
    | (have j1 := eq1772 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1772 y x
       grind)
    | exact resolve eq16 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq1886 : y = (k y x) := by grind
  clear eq1861
  have eq2072 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq406
       have i₂ := eq287 x y
       grind)
    | exact superpose eq287 eq406
    | (have j1 := eq287 x y
       grind)
    | exact resolve eq406 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2075 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq2072
  have eq2076 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2075
       have i₂ := eq1886
       grind)
    | exact superpose eq1886 eq2075
    | exact resolve eq2075 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2077 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2076
       have i₂ := eq1886
       grind)
    | exact superpose eq1886 eq2076
    | exact resolve eq2076 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076
  have eq2078 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq406
       have i₂ := eq2077
       grind)
    | exact superpose eq2077 eq406
    | exact resolve eq406 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq2077
  have eq2094 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2078
  have eq2095 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2094
       have i₂ := eq1886
       grind)
    | exact superpose eq1886 eq2094
    | exact resolve eq2094 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094
  have eq2096 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2095
  have eq2098 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2096
       grind)
    | exact superpose eq2096 eq16
    | exact resolve eq16 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq2131 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2098
       have i₂ := eq287 x y
       grind)
    | exact superpose eq287 eq2098
    | (have j1 := eq287 x y
       grind)
    | exact resolve eq2098 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq2134 : (M.op x y) = (k y x) := by grind
  clear eq2131
  have eq2136 : y = (M.op x y) := by
    first
    | (have i₁ := eq2134
       have i₂ := eq1886
       grind)
    | exact superpose eq1886 eq2134
    | exact resolve eq2134 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886 eq2134
  have eq2137 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2098
       have i₂ := eq2136
       grind)
    | exact superpose eq2136 eq2098
    | exact resolve eq2098 eq2136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098 eq2136
  have eq2155 : False := by grind
  exact eq2155

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X2) X0) X1) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq23 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq24 X0 X1 X2
       have j1 := eq22 X0 X1 X2
       grind)
    | (have r₁ := eq24 X0 X1 X2
       have r₂ := eq22 X0 X1 X2
       grind)
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq27 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq31 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq21 X0 X1
       grind)
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq35 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq32 X0 X1
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq32 X0 X1
       grind)
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq40 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq51 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (M.op X0 X2) X0
       have i₂ := eq21 X0 X2
       grind)
    | exact superpose eq21 eq25
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X0 X1) (M.op X0 X3))) X2) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op X0 X3) X0 X2
       have i₂ := eq21 X0 X3
       grind)
    | exact superpose eq21 eq19
    | exact resolve eq19 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op (M.op (M.op X1 X2) X0) X1) X0 X0
       have i₂ := eq19 X0 X1 X2 X0
       grind)
    | exact superpose eq19 eq25
    | exact resolve eq25 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq27
    | (have j0 := eq27 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op (M.op (M.op X1 X2) X0) X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op (M.op (M.op X1 X2) X0) X1)) (σ X0)) ∨ (σ (M.op (M.op (M.op X1 X2) X0) X1)) = (M.op (σ (M.op (M.op (M.op X1 X2) X0) X1)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq25 X0 X1 X2
       grind)
    | exact superpose eq25 eq27
    | (have j0 := eq27 (M.op (M.op (M.op X1 X2) X0) X1) X0
       grind)
    | exact resolve eq27 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq92 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (M.op X1 X2) X0) X1)) = (M.op (σ (M.op (M.op (M.op X1 X2) X0) X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op (M.op (M.op X1 X2) X0) X1)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq84 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq150 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 (M.op (σ X0) X1)
       have i₂ := eq35 (σ X0) X1
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq47
  have eq158 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq150
    | exact resolve eq150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq194 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq33 X1 X2 X0
       grind)
    | exact superpose eq33 eq21
    | exact resolve eq21 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq624 : ∀ X0 X1 X2 : G, (τ (M.op (M.op (M.op X0 X1) (σ X2)) X0)) = (k (τ (M.op (M.op (M.op X0 X1) (σ X2)) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 (M.op (M.op (M.op X0 X1) (σ X2)) X0) X2
       have i₂ := eq72 (σ X2) X0 X1
       grind)
    | exact superpose eq72 eq40
    | exact resolve eq40 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq72
  have eq1217 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (M.op X0 X1) X2) X0)) ≠ (σ (M.op (M.op (M.op X0 X1) X2) X0)) ∨ (σ (M.op (M.op (M.op X0 X1) X2) X0)) = (k (σ X2) (σ (M.op (M.op (M.op X0 X1) X2) X0))) ∨ (σ X2) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X0) (σ (M.op (M.op (M.op X1 X2) X0) X1))
       have i₂ := eq92 X0 X1 X2
       grind)
    | exact superpose eq92 eq12
    | (have j1 := eq92 X2 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ (M.op (M.op (M.op X1 X2) X0) X1))
       have r₂ := eq92 X0 X1 X2
       grind)
    | exact resolve eq12 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1250 : ∀ X0 X1 X2 : G, (σ X2) ≠ (σ (M.op (M.op (M.op X0 X1) X2) X0)) ∨ (σ X2) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq92 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq1251 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (M.op X0 X1) X2) X0)) = (k (σ X2) (σ (M.op (M.op (M.op X0 X1) X2) X0))) ∨ (σ X2) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1217 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1282 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (M.op X0 X1) X2) X0)) = (σ (k X2 (M.op (M.op (M.op X0 X1) X2) X0))) ∨ (σ X2) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1251 X0 X1 X2
       have i₂ := eq15 X2 (M.op (M.op (M.op X0 X1) X2) X0)
       grind)
    | exact superpose eq15 eq1251
    | (have j0 := eq1251 X0 X1 X2
       grind)
    | exact resolve eq1251 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1285 : ∀ X0 X1 X2 : G, (σ X2) = (σ (M.op (M.op (M.op X0 X1) X2) X0)) ∨ (σ X2) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1282 X0 X1 X2
       have i₂ := eq25 X2 X0 X1
       grind)
    | exact superpose eq25 eq1282
    | (have j0 := eq1282 X0 X1 X2
       grind)
    | exact resolve eq1282 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1282
  have eq1287 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X0)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1285 X0 X1 X2
       have j1 := eq1250 X0 X1 X2
       grind)
    | (have r₁ := eq1285 X0 X1 X2
       have r₂ := eq1250 X0 X1 X2
       grind)
    | exact resolve eq1285 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq1285
  have eq1396 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1438 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1396
  have eq1512 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq158 x (σ y)
       have i₂ := eq1438
       grind)
    | exact superpose eq1438 eq158
    | exact resolve eq158 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq1438
  have eq1541 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1512
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1512
    | exact resolve eq1512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1858 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X0) (M.op X1 X2))) = (M.op (σ X0) (σ (M.op (M.op X1 X0) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1287 X0 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq66 X1 X0 X0 X2
       grind)
    | exact superpose eq66 eq1287
    | exact resolve eq1287 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq10355 : ∀ X0 : G, (τ (M.op (M.op (σ x) (σ X0)) (σ x))) = (k (τ (M.op (M.op (σ x) (σ X0)) (σ x))) X0) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq624 (σ x) (σ y) x
       have i₂ := eq1541
       grind)
    | exact superpose eq1541 eq624
    | exact resolve eq624 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq1541
  have eq10539 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10355 X0
       have i₂ := eq21 (σ x) (σ X0)
       grind)
    | exact superpose eq21 eq10355
    | exact resolve eq10355 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10355
  have eq10570 : ∀ X0 : G, x = (k x y) ∨ x = (k x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10539 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10539
    | exact resolve eq10539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10539
  have eq13861 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq10570 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13862 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13861
  have eq19306 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq13862
       grind)
    | exact superpose eq13862 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq13862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13862
  have eq19307 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19306
  have eq26581 : y ≠ y ∨ y = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19307
       grind)
    | exact superpose eq19307 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq19307
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19307
       grind)
    | exact resolve eq12 eq19307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26801 : x ≠ y ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19307
  have eq26802 : y = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq26581
  have eq54447 : x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10570 y
       have i₂ := eq26802
       grind)
    | exact superpose eq26802 eq10570
    | exact resolve eq10570 eq26802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10570 eq26802
  have eq54466 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq54447
  have eq54476 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq54466
       have r₂ := eq26801
       grind)
    | exact resolve eq54466 eq26801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26801 eq54466
  have eq63023 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21 y x
       have i₂ := eq54476
       grind)
    | exact superpose eq54476 eq21
    | exact resolve eq21 eq54476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54476
  have eq63344 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq63023
  have eq74974 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq63344
       grind)
    | exact superpose eq63344 eq9
    | exact resolve eq9 eq63344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75325 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq128594 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1287 y y x
       have i₂ := eq74974 y
       grind)
    | exact superpose eq74974 eq1287
    | exact resolve eq1287 eq74974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq74974
  have eq144796 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21 (σ y) (σ x)
       have i₂ := eq128594
       grind)
    | exact superpose eq128594 eq21
    | exact resolve eq21 eq128594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128594
  have eq195884 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq144796
       grind)
    | exact superpose eq144796 eq16
    | exact resolve eq16 eq144796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144796
  have eq204599 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq195884
       have i₂ := eq63344
       grind)
    | exact superpose eq63344 eq195884
    | exact resolve eq195884 eq63344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63344 eq195884
  have eq204600 : x = y ∨ x = (M.op x y) := by grind
  clear eq204599
  have eq204601 : x = (M.op x y) := by
    first
    | (have r₁ := eq204600
       have r₂ := eq75325
       grind)
    | exact resolve eq204600 eq75325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75325 eq204600
  have eq219810 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq204601
       grind)
    | exact superpose eq204601 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq204601
       grind)
    | exact resolve eq12 eq204601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219823 : ∀ X0 : G, (k X0 (M.op (M.op x X0) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 x X0 y
       have i₂ := eq204601
       grind)
    | exact superpose eq204601 eq51
    | exact resolve eq51 eq204601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq219854 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op X0 (M.op (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq194 X0 x y
       have i₂ := eq204601
       grind)
    | exact superpose eq204601 eq194
    | exact resolve eq194 eq204601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq220226 : x = (k y x) := by grind
  clear eq219810
  have eq220583 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq219854 x
       have i₂ := eq21 x x
       grind)
    | exact superpose eq21 eq219854
    | exact resolve eq219854 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219854
  have eq220613 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq219823 X0
       have i₂ := eq21 x X0
       grind)
    | exact superpose eq21 eq219823
    | exact resolve eq219823 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219823
  have eq248623 : ∀ X0 : G, (σ (M.op (M.op x X0) x)) = (M.op (σ X0) (σ (M.op (M.op x X0) x))) := by
    intro X0
    first
    | (have i₁ := eq1858 X0 x y
       have i₂ := eq204601
       grind)
    | exact superpose eq204601 eq1858
    | exact resolve eq1858 eq204601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858 eq204601
  have eq249131 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq248623 x
       have i₂ := eq21 x x
       grind)
    | exact superpose eq21 eq248623
    | exact resolve eq248623 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq248623
  have eq291862 : x = y := by
    first
    | (have i₁ := eq220226
       have i₂ := eq220613 y
       grind)
    | exact superpose eq220613 eq220226
    | exact resolve eq220226 eq220613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220226 eq220613
  have eq314088 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq291862
       grind)
    | exact superpose eq291862 eq16
    | exact resolve eq16 eq291862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291862
  have eq314091 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq314088
       have i₂ := eq220583 x
       grind)
    | exact superpose eq220583 eq314088
    | exact resolve eq314088 eq220583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220583 eq314088
  have eq314092 : False := by grind
  exact eq314092

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyy_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X1) X0
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq96 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq96
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq107
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq555 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X1) (σ X0)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq52
    | (have j1 := eq63 X0 X1
       grind)
    | exact resolve eq52 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq21632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq21632
    | exact resolve eq21632 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21632
  have eq21644 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq21633
       have r₂ := eq29
       grind)
    | exact resolve eq21633 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21633
  have eq21658 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  have eq21664 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21644 eq56
    | exact resolve eq56 eq21644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21644
  have eq21698 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq21664
    | exact resolve eq21664 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21664
  have eq21709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21698 eq52
    | exact resolve eq52 eq21698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21698
  have eq21742 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq21709
    | exact resolve eq21709 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21709
  have eq21743 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21742
  have eq21757 : y = (k y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21743
  have eq22950 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq21757
       grind)
    | exact superpose eq21757 eq96
    | exact resolve eq96 eq21757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq21757
  have eq22977 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22950
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq22950
    | exact resolve eq22950 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22950
  have eq23943 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22977 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq22977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22977
  have eq23946 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq23943
    | exact resolve eq23943 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23943
  have eq23947 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq23946
  have eq78351 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23947 eq56
    | exact resolve eq56 eq23947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23947
  have eq78434 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq78351
    | exact resolve eq78351 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78351
  have eq78435 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq78434
  have eq78710 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq78435 eq52
    | exact resolve eq52 eq78435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78435
  have eq78786 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq78710
    | exact resolve eq78710 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78710
  have eq78787 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq78786
  have eq78807 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq78787
  have eq78927 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq555 x y
       have i₂ := eq78807
       grind)
    | exact superpose eq78807 eq555
    | (have j0 := eq555 x y
       grind)
    | exact resolve eq555 eq78807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq78807
  have eq78937 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78927
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq78927
    | exact resolve eq78927 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78927
  have eq78950 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78937
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq78937
    | exact resolve eq78937 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78937
  have eq78953 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq78950
    | exact resolve eq78950 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78950
  have eq78954 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq78953
  have eq78957 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78954
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq78954
    | exact resolve eq78954 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78954
  have eq78960 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78957
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq78957
    | exact resolve eq78957 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78957
  have eq78963 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78960
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq78960
    | exact resolve eq78960 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78960
  have eq78966 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78963
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq78963
    | exact resolve eq78963 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq78963
  have eq85128 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78966 eq56
    | exact resolve eq56 eq78966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78966
  have eq85211 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq85128
    | exact resolve eq85128 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85128
  have eq85212 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq85211
  have eq85243 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85212 eq52
    | exact resolve eq52 eq85212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85212
  have eq85323 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq85243
    | exact resolve eq85243 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq85243
  have eq85324 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq85323
  have eq85600 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq85324 eq29
    | exact resolve eq29 eq85324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq85324
  have eq1592264 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21658 eq108
    | exact resolve eq108 eq21658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq21658
  have eq1592355 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1592264
  have eq1592364 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1592355
       have r₂ := eq85600
       grind)
    | exact resolve eq1592355 eq85600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592355
  have eq1592506 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq1592364
  have eq1593287 : (τ (σ x)) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1592506 eq81
    | exact resolve eq81 eq1592506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq1592506
  have eq1593387 : y = (M.op x x) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq1593287
    | exact resolve eq1593287 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1593287
  have eq1593540 : x = (k x y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq1593387
       grind)
    | exact superpose eq1593387 eq52
    | exact resolve eq52 eq1593387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593387
  have eq1595161 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1593540
       grind)
    | exact superpose eq1593540 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1593540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593540
  have eq1595217 : y = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq1595161
  have eq1597401 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 x x
       have i₂ := eq1595217
       grind)
    | exact superpose eq1595217 eq52
    | exact resolve eq52 eq1595217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595217
  have eq1598039 : x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq1597401
  have eq1598251 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq1598039
       grind)
    | exact superpose eq1598039 eq56
    | exact resolve eq56 eq1598039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1598039
  have eq1598887 : x = (M.op y x) := by grind
  clear eq1598251
  have eq1599110 : y = (M.op x y) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq1598887
       grind)
    | exact superpose eq1598887 eq52
    | exact resolve eq52 eq1598887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1598887
  have eq1599759 : y = (M.op x y) := by
    first
    | (have i₁ := eq1599110
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1599110
    | exact resolve eq1599110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1599110
  have eq1599765 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1599759 eq22
    | exact resolve eq22 eq1599759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1599759
  have eq1600558 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1599765
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1599765
    | exact resolve eq1599765 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1599765
  have eq1600559 : False := by grind
  exact eq1600559

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq23
  have eq77 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq66 (σ X0) (σ X0)
       grind)
    | exact superpose eq66 eq76
    | exact resolve eq76 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq90 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq68 X1 X2 X0
       grind)
    | exact superpose eq68 eq64
    | exact resolve eq64 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq591 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq707 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq591 x y
       grind)
    | exact superpose eq591 eq16
    | (have j1 := eq591 x y
       grind)
    | exact resolve eq16 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 x
       have i₂ := eq591 x x
       grind)
    | exact superpose eq591 eq77
    | (have j1 := eq591 X0 X0
       grind)
    | exact resolve eq77 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq730 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq591 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq731 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq733 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq728 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq735 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq708 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq736 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq733 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq733
    | (have j0 := eq733 X0
       grind)
    | exact resolve eq733 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq740 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq735 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq735
    | (have j0 := eq735 X0
       grind)
    | exact resolve eq735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq747 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq731 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq731
    | (have j0 := eq731 (τ X0)
       grind)
    | exact resolve eq731 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq749 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq747 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq747
    | (have j0 := eq747 X0
       grind)
    | exact resolve eq747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq752 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq749 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq749
    | (have j0 := eq749 X0
       grind)
    | exact resolve eq749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq801 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq740 (τ X0)
       grind)
    | exact superpose eq740 eq19
    | (have j1 := eq740 (τ X0)
       grind)
    | exact resolve eq19 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq807 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq801 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq801
    | (have j0 := eq801 X0
       grind)
    | exact resolve eq801 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq823 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq807 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq807
    | (have j0 := eq807 X0
       grind)
    | exact resolve eq807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq836 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq823 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq823
    | (have j0 := eq823 X0
       grind)
    | exact resolve eq823 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq863 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq836 (τ X0)
       grind)
    | exact superpose eq836 eq19
    | (have j1 := eq836 (τ X0)
       grind)
    | exact resolve eq19 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq863 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq863
    | (have j0 := eq863 X0
       grind)
    | exact resolve eq863 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq885 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq869 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq869
    | (have j0 := eq869 X0
       grind)
    | exact resolve eq869 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq972 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq885 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq885
    | (have j0 := eq885 (σ X0)
       grind)
    | exact resolve eq885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1006 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq972 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq972
    | (have j0 := eq972 X0
       grind)
    | exact resolve eq972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1021 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1006 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1006
    | (have j0 := eq1006 X0
       grind)
    | exact resolve eq1006 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq8453 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq736 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq736
    | exact resolve eq736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8475 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq736 X0
       grind)
    | exact superpose eq736 eq77
    | (have j1 := eq736 X0
       grind)
    | exact resolve eq77 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq736
  have eq8535 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8475 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8475
    | (have j0 := eq8475 X0
       grind)
    | exact resolve eq8475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8475
  have eq8538 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8453 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq8453
    | (have j0 := eq8453 X0
       grind)
    | exact resolve eq8453 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8453
  have eq8542 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (σ (k (k (τ X0) (τ X0)) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8538 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8538
    | (have j0 := eq8538 X0
       grind)
    | exact resolve eq8538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8538
  have eq8544 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8542 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq8542
    | (have j0 := eq8542 X0
       grind)
    | exact resolve eq8542 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8542
  have eq8545 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8544 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq8544
    | (have j0 := eq8544 X0
       grind)
    | exact resolve eq8544 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8544
  have eq8546 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8545 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8545
    | (have j0 := eq8545 X0
       grind)
    | exact resolve eq8545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8545
  have eq8634 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq836 X0
       have i₂ := eq8546 X0
       grind)
    | exact superpose eq8546 eq836
    | (have j0 := eq836 X0
       have j1 := eq8546 X0
       grind)
    | exact resolve eq836 eq8546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq8546
  have eq8689 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8634
  have eq8785 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 (k X0 X0) X1
       have i₂ := eq8689 X0
       grind)
    | exact superpose eq8689 eq68
    | (have j1 := eq8689 X0
       grind)
    | exact resolve eq68 eq8689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8689
  have eq9080 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 X0 X0 X0
       have i₂ := eq8785 X0 X1
       grind)
    | exact superpose eq8785 eq90
    | (have j1 := eq8785 X0 X2
       grind)
    | exact resolve eq90 eq8785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8785
  have eq9149 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9080 X0 X1 X2
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9080
    | (have j0 := eq9080 X0 X1 X2
       grind)
    | exact resolve eq9080 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9080
  have eq9578 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9149 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9149
  have eq9579 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9578 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9578
  have eq9614 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq9579 X0
       grind)
    | exact superpose eq9579 eq9
    | exact resolve eq9 eq9579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9616 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 (k X0 X0) X0 X0
       have i₂ := eq9579 X0
       grind)
    | exact superpose eq9579 eq65
    | exact resolve eq65 eq9579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9579
  have eq9678 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9616 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq9616
    | exact resolve eq9616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9679 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9616 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq9616
    | exact resolve eq9616 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq9616
  have eq9725 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9614 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq9614
    | exact resolve eq9614 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9614
  have eq10266 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9725 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq9725
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq9725 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9725
  have eq10330 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10266
  have eq17310 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq588 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq588
    | exact resolve eq588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq17420 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17310 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17310
    | (have j0 := eq17310 X0 X1
       grind)
    | exact resolve eq17310 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17310
  have eq25006 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8535 X0
       have i₂ := eq17420 X0 X0
       grind)
    | exact superpose eq17420 eq8535
    | (have j0 := eq8535 X0
       have j1 := eq17420 X0 X0
       grind)
    | exact resolve eq8535 eq17420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8535
  have eq25094 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25006 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25006
  have eq25123 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25094 X0
       have j1 := eq752 X0
       grind)
    | (have r₁ := eq25094 X0
       have r₂ := eq752 X0
       grind)
    | exact resolve eq25094 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq25094
  have eq25635 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10330 X0
       have i₂ := eq25123 X0
       grind)
    | exact superpose eq25123 eq10330
    | (have j0 := eq10330 X0
       have j1 := eq25123 X0
       grind)
    | exact resolve eq10330 eq25123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10330 eq25123
  have eq25708 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25635 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25635
  have eq25817 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1021 X0
       have i₂ := eq25708 X0
       grind)
    | exact superpose eq25708 eq1021
    | (have j0 := eq1021 X0
       have j1 := eq25708 X0
       grind)
    | exact resolve eq1021 eq25708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq25708
  have eq25890 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25817
  have eq26011 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq25890 X0
       grind)
    | exact superpose eq25890 eq10
    | (have j1 := eq25890 X0
       grind)
    | exact resolve eq10 eq25890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25890
  have eq26078 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq26011 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq26011
    | (have j0 := eq26011 X0
       grind)
    | exact resolve eq26011 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26011
  have eq26133 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq26078
  have eq26264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26133 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26133
  have eq26366 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9678 X0
       have i₂ := eq26264 X0
       grind)
    | exact superpose eq26264 eq9678
    | exact resolve eq9678 eq26264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9678
  have eq26367 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9679 X0
       have i₂ := eq26264 X0
       grind)
    | exact superpose eq26264 eq9679
    | exact resolve eq9679 eq26264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9679
  have eq26441 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26264 (σ X0)
       grind)
    | exact superpose eq26264 eq15
    | exact resolve eq15 eq26264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26500 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq26441 X0
       have i₂ := eq26264 X0
       grind)
    | exact superpose eq26264 eq26441
    | exact resolve eq26441 eq26264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26264 eq26441
  have eq26766 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq26366 X0
       grind)
    | exact superpose eq26366 eq90
    | exact resolve eq90 eq26366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26942 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) = (M.op X1 (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq26367 X0
       grind)
    | exact superpose eq26367 eq90
    | exact resolve eq90 eq26367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26367
  have eq38715 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq707
       have i₂ := eq17420 x y
       grind)
    | exact superpose eq17420 eq707
    | (have j1 := eq17420 (σ x) (σ y)
       grind)
    | (have r₁ := eq707
       have r₂ := eq17420 x y
       grind)
    | exact resolve eq707 eq17420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq17420
  have eq38716 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq38715
  have eq38718 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq38716
       have i₂ := eq26500 x
       grind)
    | exact superpose eq26500 eq38716
    | exact resolve eq38716 eq26500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26500 eq38716
  have eq1213075 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 y x
       have i₂ := eq38718
       grind)
    | exact superpose eq38718 eq66
    | exact resolve eq66 eq38718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38718
  have eq1257628 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq68 (σ y) (σ x) X0
       have i₂ := eq1213075
       grind)
    | exact superpose eq1213075 eq68
    | exact resolve eq68 eq1213075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1213075
  have eq1258279 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1257628 X0
       have i₂ := eq64 (σ y) X0
       grind)
    | exact superpose eq64 eq1257628
    | exact resolve eq1257628 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257628
  have eq1258706 : ∀ X0 : G, (M.op x x) = (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1258279 X0
       grind)
    | exact superpose eq1258279 eq10
    | (have j1 := eq1258279 X0
       grind)
    | exact resolve eq10 eq1258279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258279
  have eq1259268 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1258706 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1258706
    | (have j0 := eq1258706 X0
       grind)
    | exact resolve eq1258706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258706
  have eq1259269 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op x x) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1259268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259268
  have eq1259632 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x x) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 y y
       have i₂ := eq1259269 X0
       grind)
    | exact superpose eq1259269 eq90
    | (have j1 := eq1259269 X1
       grind)
    | exact resolve eq90 eq1259269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1259269
  have eq1260013 : ∀ X0 X1 : G, y = (M.op x x) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1259632 X1 X1
       have i₂ := eq64 y X1
       grind)
    | exact superpose eq64 eq1259632
    | (have j0 := eq1259632 X0 X1
       grind)
    | exact resolve eq1259632 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259632
  have eq1262437 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26366 x
       have i₂ := eq1260013 X0 X1
       grind)
    | exact superpose eq1260013 eq26366
    | (have j1 := eq1260013 X0 (σ x)
       grind)
    | exact resolve eq26366 eq1260013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26366
  have eq1262723 : ∀ X0 X1 : G, y = (M.op x y) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 x x
       have i₂ := eq1260013 X0 X1
       grind)
    | exact superpose eq1260013 eq66
    | (have j1 := eq1260013 x X1
       grind)
    | exact resolve eq66 eq1260013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1260013
  have eq1264856 : ∀ X0 : G, y ≠ y ∨ y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1262723 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262723
  have eq1264857 : ∀ X0 : G, y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1264856 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264856
  have eq1264864 : ∀ X0 X1 X2 : G, (M.op (σ y) X2) = X2 ∨ (M.op (M.op (M.op X0 X1) (M.op (M.op y X0) x)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 x y X1
       have i₂ := eq1264857 X2
       grind)
    | exact superpose eq1264857 eq62
    | (have j1 := eq1264857 X2
       grind)
    | exact resolve eq62 eq1264857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1264857
  have eq1274457 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (σ y)) X0) (τ (σ y))) = (M.op X0 (M.op (M.op (τ (σ y)) X0) (τ (σ y)))) ∨ (M.op (M.op (M.op X1 X2) (M.op (M.op y X1) x)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26942 (σ y) X1
       have i₂ := eq1264864 X0 X1 (σ y)
       grind)
    | exact superpose eq1264864 eq26942
    | (have j1 := eq1264864 X1 X2 X2
       grind)
    | exact resolve eq26942 eq1264864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26942 eq1264864
  have eq1275155 : ∀ X0 X1 X2 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (M.op (M.op (M.op X1 X2) (M.op (M.op y X1) x)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1274457 X1 X1 X2
       have i₂ := eq64 (τ (σ y)) X1
       grind)
    | exact superpose eq64 eq1274457
    | (have j0 := eq1274457 X0 X1 X2
       grind)
    | exact resolve eq1274457 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274457
  have eq1275283 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op y X1) x)) X2) = X2 ∨ y = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1275155 X0 X1 X2
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1275155
    | (have j0 := eq1275155 X0 X1 X2
       grind)
    | exact resolve eq1275155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275155
  have eq1277409 : ∀ X0 : G, y ≠ y ∨ y = (M.op (M.op (M.op X0 y) (M.op (M.op y X0) x)) y) := by
    intro X0
    first
    | (have j0 := eq1275283 (M.op (M.op X0 y) (M.op (M.op y X0) x)) X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275283
  have eq1277410 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) (M.op (M.op y X0) x)) y) := by
    intro X0
    first
    | (have j0 := eq1277409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277409
  have eq1278153 : y = (M.op (M.op (M.op y y) x) y) := by
    first
    | (have i₁ := eq65 (M.op (M.op y y) x) y y
       have i₂ := eq1277410 y
       grind)
    | exact superpose eq1277410 eq65
    | exact resolve eq65 eq1277410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277410
  have eq1281384 : y = (M.op x y) := by
    first
    | (have i₁ := eq65 x y y
       have i₂ := eq1278153
       grind)
    | exact superpose eq1278153 eq65
    | exact resolve eq65 eq1278153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1278153
  have eq1328786 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ y = (M.op X0 y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1262437 X0 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262437
  have eq1328787 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1328786 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328786
  have eq1328890 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq64 (σ y) (σ x)
       have i₂ := eq1328787 X0
       grind)
    | exact superpose eq1328787 eq64
    | (have j1 := eq1328787 X0
       grind)
    | exact resolve eq64 eq1328787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328787
  have eq1329265 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1328890 X0
       grind)
    | exact superpose eq1328890 eq16
    | (have j1 := eq1328890 X0
       grind)
    | exact resolve eq16 eq1328890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328890
  have eq1329687 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1329265 X0
       have i₂ := eq1281384
       grind)
    | exact superpose eq1281384 eq1329265
    | (have j0 := eq1329265 X0
       grind)
    | exact resolve eq1329265 eq1281384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281384 eq1329265
  have eq1329688 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1329687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329687
  have eq1329759 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq26766 y x
       have i₂ := eq1329688 y
       grind)
    | exact superpose eq1329688 eq26766
    | exact resolve eq26766 eq1329688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26766
  have eq1331683 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1329759 x
       have i₂ := eq64 (σ y) x
       grind)
    | exact superpose eq64 eq1329759
    | exact resolve eq1329759 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1329759
  have eq1338476 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1331683 (σ x)
       grind)
    | exact superpose eq1331683 eq16
    | exact resolve eq16 eq1331683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331683
  have eq1338873 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1338476
       have i₂ := eq1329688 x
       grind)
    | exact superpose eq1329688 eq1338476
    | exact resolve eq1338476 eq1329688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329688 eq1338476
  have eq1338874 : False := by grind
  exact eq1338874

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq95 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq52 eq90
    | exact resolve eq90 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq96 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq95
    | exact resolve eq95 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq58 eq96
    | exact resolve eq96 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq96
  have eq105 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq105
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq662 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X1) (σ X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq51
    | (have j1 := eq62 X0 X1
       grind)
    | exact resolve eq51 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq802 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x) X0 (σ y)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq57 X1 X2 X0
       grind)
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq10276 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq97 eq94
    | exact resolve eq94 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq97
  have eq10292 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq10276
    | exact resolve eq10276 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10276
  have eq24972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24979 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq24972
    | exact resolve eq24972 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24972
  have eq24990 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24979
       have r₂ := eq28
       grind)
    | exact resolve eq24979 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24979
  have eq24996 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24990 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq24990
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq24990
       grind)
    | exact resolve eq12 eq24990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24990
  have eq25045 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq24996
  have eq25046 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq25045
  have eq25487 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25046 eq117
    | exact resolve eq117 eq25046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25046
  have eq25502 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq25487
  have eq25525 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq25502
  have eq73223 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25525 eq117
    | exact resolve eq117 eq25525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq25525
  have eq73241 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq73223
  have eq73310 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq834 X0 y x
       have i₂ := eq73241
       grind)
    | exact superpose eq73241 eq834
    | exact resolve eq834 eq73241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq73241
  have eq73387 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq73310 x
       have i₂ := eq51 y x
       grind)
    | exact superpose eq51 eq73310
    | exact resolve eq73310 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73310
  have eq74276 : ∀ X0 : G, y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq55 x x
       have i₂ := eq73387 X0
       grind)
    | exact superpose eq73387 eq55
    | (have j1 := eq73387 x
       grind)
    | exact resolve eq55 eq73387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq73387
  have eq74366 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74276 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74276
    | (have j0 := eq74276 X0
       grind)
    | exact resolve eq74276 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74276
  have eq74568 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq74366 x
       grind)
    | exact superpose eq74366 eq19
    | (have j1 := eq74366 x
       grind)
    | exact resolve eq19 eq74366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq74366
  have eq74718 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq74568
  have eq75061 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74718 eq30
    | exact resolve eq30 eq74718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq74718
  have eq75227 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq75061
    | exact resolve eq75061 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq75061
  have eq75228 : y = (M.op x y) := by grind
  clear eq75227
  have eq75229 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq75228 eq21
    | exact resolve eq21 eq75228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq75232 : x = (M.op y x) := by
    first
    | exact superpose eq75228 eq52
    | exact resolve eq52 eq75228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq75378 : x = (k x y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq75228 eq10292
    | exact resolve eq10292 eq75228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10292 eq75228
  have eq75517 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq75229
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq75229
    | exact resolve eq75229 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75229
  have eq75518 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq75517 eq27
    | exact resolve eq27 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq75583 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq75517 eq802
    | exact resolve eq802 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq83257 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq662 x y
       have i₂ := eq75378
       grind)
    | exact superpose eq75378 eq662
    | (have j0 := eq662 x y
       grind)
    | exact resolve eq662 eq75378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75378
  have eq83266 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83257
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq83257
    | exact resolve eq83257 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83257
  have eq83282 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq75517 eq83266
    | exact resolve eq83266 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83266
  have eq83296 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83282
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq83282
    | exact resolve eq83282 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83282
  have eq83302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq75518 eq83296
    | exact resolve eq83296 eq75518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83296
  have eq83307 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq83302
       have r₂ := eq28
       grind)
    | exact resolve eq83302 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83302
  have eq83312 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83307
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq83307
    | exact resolve eq83307 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83307
  have eq83317 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq75517 eq83312
    | exact resolve eq83312 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83312
  have eq83322 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83317
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq83317
    | exact resolve eq83317 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83317
  have eq83327 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq75518 eq83322
    | exact resolve eq83322 eq75518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83322
  have eq83332 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83327
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq83327
    | exact resolve eq83327 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83327
  have eq83336 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq75517 eq83332
    | exact resolve eq83332 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83332
  have eq83339 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83336
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq83336
    | exact resolve eq83336 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83336
  have eq120705 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq83339 eq51
    | exact resolve eq51 eq83339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83339
  have eq120822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq75518 eq120705
    | exact resolve eq120705 eq75518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120705
  have eq120826 : x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq120822
       have r₂ := eq28
       grind)
    | exact resolve eq120822 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120822
  have eq120857 : x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq120826
  have eq121023 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq662 x y
       have i₂ := eq120857
       grind)
    | exact superpose eq120857 eq662
    | (have j0 := eq662 x y
       grind)
    | exact resolve eq662 eq120857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120857
  have eq121030 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121023
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq121023
    | exact resolve eq121023 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121023
  have eq121048 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75517 eq121030
    | exact resolve eq121030 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121030
  have eq121062 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121048
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq121048
    | exact resolve eq121048 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121048
  have eq121068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75518 eq121062
    | exact resolve eq121062 eq75518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121062
  have eq121073 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq121068
       have r₂ := eq28
       grind)
    | exact resolve eq121068 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121068
  have eq121078 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121073
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq121073
    | exact resolve eq121073 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121073
  have eq121084 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75517 eq121078
    | exact resolve eq121078 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121078
  have eq121090 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121084
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq121084
    | exact resolve eq121084 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121084
  have eq121095 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq75518 eq121090
    | exact resolve eq121090 eq75518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121090
  have eq121096 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq121095
  have eq121101 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq121096
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq121096
    | exact resolve eq121096 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121096
  have eq121105 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq75517 eq121101
    | exact resolve eq121101 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121101
  have eq121108 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq121105
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq121105
    | exact resolve eq121105 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121105
  have eq122188 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq121108 eq51
    | exact resolve eq51 eq121108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq121108
  have eq122305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq75518 eq122188
    | exact resolve eq122188 eq75518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122188
  have eq122309 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq122305
       have r₂ := eq28
       grind)
    | exact resolve eq122305 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122305
  have eq122316 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq122309 eq53
    | exact resolve eq53 eq122309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122309
  have eq123564 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq122316 eq75583
    | exact resolve eq75583 eq122316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75583 eq122316
  have eq123715 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq53 eq123564
    | exact resolve eq123564 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq123564
  have eq123741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq75518 eq123715
    | exact resolve eq123715 eq75518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123715
  have eq123755 : x = y := by
    first
    | (have r₁ := eq123741
       have r₂ := eq28
       grind)
    | exact resolve eq123741 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123741
  have eq123762 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq123755
       grind)
    | exact superpose eq123755 eq25
    | exact resolve eq25 eq123755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq123941 : x = (M.op x x) := by
    first
    | (have i₁ := eq75232
       have i₂ := eq123755
       grind)
    | exact superpose eq123755 eq75232
    | exact resolve eq75232 eq123755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75232 eq123755
  have eq124166 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq75517 eq123762
    | exact resolve eq123762 eq75517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75517 eq123762
  have eq124299 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq124166
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq124166
    | exact resolve eq124166 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124166
  have eq125480 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq124299 eq75518
    | exact resolve eq75518 eq124299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75518
  have eq125804 : x = (k x x) := by grind
  clear eq123941
  have eq128597 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq662 x x
       have i₂ := eq125804
       grind)
    | exact superpose eq125804 eq662
    | (have j0 := eq662 x x
       grind)
    | exact resolve eq662 eq125804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq125804
  have eq128602 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq128597
  have eq128615 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq128602
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq128602
    | exact resolve eq128602 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq128602
  have eq128634 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq124299 eq128615
    | exact resolve eq128615 eq124299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124299 eq128615
  have eq128653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125480 eq128634
    | exact resolve eq128634 eq125480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125480 eq128634
  have eq128671 : False := by grind
  exact eq128671

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_x_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq105 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq105
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq661 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq62 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq62 X0 X0
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq669 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq661 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq661
    | (have j0 := eq661 X0 X1
       grind)
    | exact resolve eq661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq834 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq57 X1 X2 X0
       grind)
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25074
    | exact resolve eq25074 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25074
  have eq25092 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq25081
       have r₂ := eq28
       grind)
    | exact resolve eq25081 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25081
  have eq25105 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq25092 eq57
    | exact resolve eq57 eq25092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq25182 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq25105 x
       have i₂ := eq51 sF3 x
       grind)
    | exact superpose eq51 eq25105
    | exact resolve eq25105 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25105
  have eq25601 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq55 X0 x
       have i₂ := eq25182 (M.op X0 x)
       grind)
    | exact superpose eq25182 eq55
    | (have j1 := eq25182 X0
       grind)
    | exact resolve eq55 eq25182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25182
  have eq25646 : ∀ X0 : G, y = (M.op y x) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq27 eq25601
    | (have j0 := eq25601 X0
       grind)
    | exact resolve eq25601 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25601
  have eq25658 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq51 y x
       have i₂ := eq25646 X0
       grind)
    | exact superpose eq25646 eq51
    | (have j1 := eq25646 X0
       grind)
    | exact resolve eq51 eq25646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25646
  have eq26063 : ∀ X0 : G, y = (k y y) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    grind
  clear eq25658
  have eq50289 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq669 y y
       have i₂ := eq26063 X0
       grind)
    | exact superpose eq26063 eq669
    | (have j0 := eq669 y y
       have j1 := eq26063 (σ y)
       grind)
    | exact resolve eq669 eq26063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq26063
  have eq50292 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq50289 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50289
  have eq50293 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq50292 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50292
  have eq50305 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq50293 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq50293
    | (have j0 := eq50293 (σ y)
       grind)
    | exact resolve eq50293 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50293
  have eq52447 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq50305 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50305
  have eq52448 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq52447
  have eq52540 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq52448 eq834
    | exact resolve eq834 eq52448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52448
  have eq52593 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52540 x
       have i₂ := eq51 sF3 x
       grind)
    | exact superpose eq51 eq52540
    | exact resolve eq52540 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52540
  have eq53211 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq52593 eq27
    | (have j1 := eq52593 (σ x)
       grind)
    | exact resolve eq27 eq52593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52593
  have eq53278 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53211
  have eq53303 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53278
  have eq53674 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq53303
       grind)
    | exact superpose eq53303 eq105
    | exact resolve eq105 eq53303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq53303
  have eq53703 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53674
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq53674
    | exact resolve eq53674 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53674
  have eq54126 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53703 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq53703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53703
  have eq54133 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq54126
    | exact resolve eq54126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54126
  have eq54134 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq54133
  have eq61353 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq54134 eq834
    | exact resolve eq834 eq54134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54134
  have eq61422 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61353 x
       have i₂ := eq51 sF3 x
       grind)
    | exact superpose eq51 eq61353
    | exact resolve eq61353 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61353
  have eq61933 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq61422 eq55
    | (have j1 := eq61422 (σ x)
       grind)
    | exact resolve eq55 eq61422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61422
  have eq62011 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61933
    | (have j0 := eq61933 (σ x)
       grind)
    | exact resolve eq61933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61933
  have eq62012 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq62011 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62011
  have eq62551 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62012 eq27
    | (have j1 := eq62012 (σ x)
       grind)
    | exact resolve eq27 eq62012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62012
  have eq62618 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq62551
  have eq62625 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq62618 eq28
    | exact resolve eq28 eq62618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq62627 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq62618 eq53
    | exact resolve eq53 eq62618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq62618
  have eq63022 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25092 eq62627
    | exact resolve eq62627 eq25092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25092
  have eq226371 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq63022
  have eq242771 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq226371 eq117
    | exact resolve eq117 eq226371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq226371
  have eq242796 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq242771
  have eq242804 : y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq242796
       have r₂ := eq62625
       grind)
    | exact resolve eq242796 eq62625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242796
  have eq242905 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq834 X0 y x
       have i₂ := eq242804
       grind)
    | exact superpose eq242804 eq834
    | exact resolve eq834 eq242804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq242804
  have eq243176 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq242905 x
       have i₂ := eq51 y x
       grind)
    | exact superpose eq51 eq242905
    | exact resolve eq242905 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq242905
  have eq244276 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq55 x x
       have i₂ := eq243176 X0
       grind)
    | exact superpose eq243176 eq55
    | (have j1 := eq243176 x
       grind)
    | exact resolve eq55 eq243176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq243176
  have eq244506 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq244276 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq244276
    | (have j0 := eq244276 X0
       grind)
    | exact resolve eq244276 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244276
  have eq245610 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq244506 x
       grind)
    | exact superpose eq244506 eq19
    | (have j1 := eq244506 x
       grind)
    | exact resolve eq19 eq244506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244506
  have eq245822 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq245610
  have eq245886 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq245822 eq30
    | exact resolve eq30 eq245822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq245822
  have eq246538 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq245886
    | exact resolve eq245886 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245886
  have eq246576 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq246538 eq21
    | exact resolve eq21 eq246538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246538
  have eq246997 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq246576
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq246576
    | exact resolve eq246576 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246576
  have eq246998 : x = y := by
    first
    | (have r₁ := eq246997
       have r₂ := eq62625
       grind)
    | exact resolve eq246997 eq62625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246997
  have eq247000 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq246998
       grind)
    | exact superpose eq246998 eq19
    | exact resolve eq19 eq246998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq247001 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq246998
       grind)
    | exact superpose eq246998 eq25
    | exact resolve eq25 eq246998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq246998
  have eq247452 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq247001
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq247001
    | exact resolve eq247001 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247001
  have eq247678 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq247452 eq62625
    | exact resolve eq62625 eq247452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62625
  have eq247680 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq247452 eq62627
    | exact resolve eq62627 eq247452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62627 eq247452
  have eq248802 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq247680
  have eq250736 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq248802 eq74
    | exact resolve eq74 eq248802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq248802
  have eq250817 : x = (k x x) := by
    first
    | exact superpose eq29 eq250736
    | exact resolve eq250736 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq250736
  have eq264481 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq250817
       grind)
    | exact superpose eq250817 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq250817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250817
  have eq264497 : x = (M.op x x) := by grind
  clear eq264481
  have eq264513 : x = (M.op x y) := by
    first
    | (have i₁ := eq264497
       have i₂ := eq247000
       grind)
    | exact superpose eq247000 eq264497
    | exact resolve eq264497 eq247000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247000 eq264497
  have eq264582 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq264513 eq21
    | exact resolve eq21 eq264513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq264513
  have eq265162 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq264582
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq264582
    | exact resolve eq264582 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq264582
  have eq265282 : False := by grind
  exact eq265282
